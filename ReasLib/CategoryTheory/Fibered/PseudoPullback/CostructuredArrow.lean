/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Comma indices of a based pseudo-pullback

The reverse index construction pulls back the given object of the second category along the
base map of a comma arrow. The target groupoid fibration supplies the actual vertical comparison
between the two Cartesian lifts. These are the index data needed to transport direct-image
sections through a base-change square.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped BasedFunctor
noncomputable section

universe u v uX vX uY vY uS vS
namespace CategoryTheory.BasedCategory.PseudoPullback.CostructuredArrow

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

/-- Comma indices over a specified object on the second side of the pseudo-pullback. -/
abbrev source (y : Y.obj) :=
  CategoryTheory.CostructuredArrow (PseudoPullback.snd F G).toFunctor y

/-- Comma indices of the original first functor at the image of the specified object. -/
abbrev target (y : Y.obj) :=
  CategoryTheory.CostructuredArrow F.toFunctor (G.obj y)

/-- The stored pseudo-pullback comparison followed by the given comma arrow. -/
def forwardObj (y : Y.obj) (a : source F G y) : target F G y :=
  CategoryTheory.CostructuredArrow.mk
    ((comparisonIsoApp a.left).hom ≫ G.map a.hom)

/-- Forward transport keeps the first component of the given pseudo-pullback arrow. -/
def forwardMap (y : Y.obj) {a b : source F G y} (k : a ⟶ b) :
    forwardObj F G y a ⟶ forwardObj F G y b :=
  CategoryTheory.CostructuredArrow.homMk (fstMap k.left) (by sorry)

/-- The actual forward functor on comma indices. -/
def forward (y : Y.obj) : source F G y ⥤ target F G y where
  obj := forwardObj F G y
  map := forwardMap F G y
  map_id := sorry
  map_comp := sorry

section Reverse
variable [Functor.IsFibered.InGroupoids Y.p] [Functor.IsFibered.InGroupoids S.p]

/-- A groupoid fibration's given Cartesian data may be read at any specified lift of the
same base arrow. This transports its existing witness, without asserting a new lifting factory. -/
theorem cartesianOfHomLift {A : Type*} [Category A] (p : A ⥤ C)
    [Functor.IsFibered.InGroupoids p] {R T : C} (r : R ⟶ T)
    {a b : A} (f : a ⟶ b) [p.IsHomLift r f] : p.IsCartesian r f := by
  subst_hom_lift p r f
  infer_instance

/-- The actual base arrow of a comma index, with the based-functor endpoint equalities. -/
def reverseBase (y : Y.obj) (a : target F G y) : X.p.obj a.left ⟶ Y.p.obj y :=
  eqToHom (F.w_obj a.left).symm ≫ S.p.map a.hom ≫ eqToHom (G.w_obj y)

/-- Pull back the supplied second-side object by the actual base arrow. -/
def reversePoint (y : Y.obj) (a : target F G y) : Y.obj :=
  Functor.IsPreFibered.pullbackObj (p := Y.p) rfl (reverseBase F G y a)

/-- The given fibration's actual Cartesian arrow from that pullback to the original object. -/
def reverseArrow (y : Y.obj) (a : target F G y) : reversePoint F G y a ⟶ y :=
  Functor.IsPreFibered.pullbackMap (p := Y.p) rfl (reverseBase F G y a)

/-- The two lifts to the target fibration have the same specified base arrow. -/
theorem reverseArrow_image_isHomLift (y : Y.obj) (a : target F G y) :
    S.p.IsHomLift (S.p.map a.hom) (G.map (reverseArrow F G y a)) := sorry

/-- The comparison uses the two actual Cartesian lifts in the given target fibration. -/
def reverseComparison (y : Y.obj) (a : target F G y) :
    F.obj a.left ≅ G.obj (reversePoint F G y a) := by
  letI := reverseArrow_image_isHomLift F G y a
  letI := cartesianOfHomLift S.p (S.p.map a.hom) (G.map (reverseArrow F G y a))
  exact Functor.IsCartesian.domainUniqueUpToIso S.p (S.p.map a.hom)
    (G.map (reverseArrow F G y a)) a.hom

/-- Reverse comma indices have the original first object, the actual pulled-back second
object, and the specified Cartesian comparison in their common fibre. -/
def reversePair (y : Y.obj) (a : target F G y) : (PseudoPullback F G).obj :=
  PseudoPullback.mk F G (X.p.obj a.left)
    { fst := ⟨a.left, rfl⟩
      snd := ⟨reversePoint F G y a, Functor.IsPreFibered.pullbackObj_proj _ _⟩
      iso :=
        { hom := Functor.Fiber.Hom.mk (reverseComparison F G y a).hom (by sorry)
          inv := Functor.Fiber.Hom.mk (reverseComparison F G y a).inv (by sorry)
          hom_inv_id := sorry
          inv_hom_id := sorry } }

/-- The reverse index over the original second-side object. -/
def reverseObj (y : Y.obj) (a : target F G y) : source F G y :=
  CategoryTheory.CostructuredArrow.mk (Y := reversePair F G y a) (reverseArrow F G y a)

/-- The base arrow needed to map the actual pulled-back second objects. -/
def reverseMapBase (y : Y.obj) {a b : target F G y} (k : a ⟶ b) :
    Y.p.obj (reversePoint F G y a) ⟶ X.p.obj b.left :=
  eqToHom (Functor.IsPreFibered.pullbackObj_proj rfl (reverseBase F G y a)) ≫
    X.p.map k.left

/-- Comma commutativity supplies the base factorization for the Cartesian lift. -/
theorem reverseMapBase_fac (y : Y.obj) {a b : target F G y} (k : a ⟶ b) :
    Y.p.map (reverseArrow F G y a) =
      reverseMapBase F G y k ≫ reverseBase F G y b := sorry

/-- The second component of a reverse index map is the native Cartesian factor map. -/
def reversePointMap (y : Y.obj) {a b : target F G y} (k : a ⟶ b) :
    reversePoint F G y a ⟶ reversePoint F G y b := by
  letI : Y.p.IsCartesian (reverseBase F G y b) (reverseArrow F G y b) :=
    Functor.IsPreFibered.pullbackMap.IsCartesian rfl (reverseBase F G y b)
  letI : Y.p.IsStronglyCartesian (reverseBase F G y b) (reverseArrow F G y b) :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Y.p _ _
  letI : Y.p.IsHomLift (reverseBase F G y a) (reverseArrow F G y a) :=
    inferInstanceAs (Y.p.IsHomLift (reverseBase F G y a)
      (Functor.IsPreFibered.pullbackMap (p := Y.p) rfl (reverseBase F G y a)))
  exact Functor.IsStronglyCartesian.map Y.p (reverseBase F G y b)
    (reverseArrow F G y b) (reverseMapBase_fac F G y k) (reverseArrow F G y a)

/-- The actual pair of reverse component maps forms a pseudo-pullback arrow. -/
def reversePairMap (y : Y.obj) {a b : target F G y} (k : a ⟶ b) :
    reversePair F G y a ⟶ reversePair F G y b :=
  PseudoPullback.Hom.mk (X.p.map k.left) k.left (by sorry)
    (reversePointMap F G y k) (by sorry) (by sorry)

/-- The reverse comma map stores those two component maps. -/
def reverseMap (y : Y.obj) {a b : target F G y} (k : a ⟶ b) :
    reverseObj F G y a ⟶ reverseObj F G y b :=
  CategoryTheory.CostructuredArrow.homMk (reversePairMap F G y k) (by sorry)

/-- The actual reverse functor built from the given Cartesian pullbacks. -/
def reverse (y : Y.obj) : target F G y ⥤ source F G y where
  obj := reverseObj F G y
  map := reverseMap F G y
  map_id := sorry
  map_comp := sorry

/-- The reverse Cartesian arrow at a forward index lies over the original second arrow. -/
theorem unitArrow_isHomLift (y : Y.obj) (a : source F G y) :
    Y.p.IsHomLift (Y.p.map a.hom)
      (reverseArrow F G y (forwardObj F G y a)) := sorry

/-- The original second object and its reconstructed Cartesian pullback have their native
comparison in both directions, supplied by the given groupoid fibration. -/
def unitSecondIso (y : Y.obj) (a : source F G y) :
    sndObj a.left ≅ reversePoint F G y (forwardObj F G y a) := by
  letI originalCartesian : Y.p.IsCartesian (Y.p.map a.hom) a.hom :=
    Functor.IsFibered.InGroupoids.all_isCartesian (p := Y.p) a.hom
  letI reconstructedLift := unitArrow_isHomLift F G y a
  letI reconstructedCartesian := cartesianOfHomLift Y.p (Y.p.map a.hom)
    (reverseArrow F G y (forwardObj F G y a))
  exact @Functor.IsCartesian.domainUniqueUpToIso C Y.obj _ _ Y.p _ _ _ _
    (Y.p.map a.hom) (reverseArrow F G y (forwardObj F G y a))
    reconstructedCartesian _ a.hom originalCartesian

/-- The unit comparison on pseudo-pullback objects keeps the first object and uses the
native Cartesian comparison on the second object. -/
def unitPairIso (y : Y.obj) (a : source F G y) :
    a.left ≅ reversePair F G y (forwardObj F G y a) :=
  PseudoPullback.mkIso (fstBaseIso a.left).symm (Iso.refl _) (unitSecondIso F G y a)
    (by sorry) (by sorry) (by sorry)

/-- The unit of the index equivalence stores those actual pseudo-pullback maps. -/
def unitApp (y : Y.obj) (a : source F G y) :
    a ≅ (forward F G y ⋙ reverse F G y).obj a :=
  CategoryTheory.CostructuredArrow.isoMk (unitPairIso F G y a) (by sorry)

/-- The counit uses the identity of the original first object. Its comma compatibility is
the factorization law of the given Cartesian lifts. -/
def counitApp (y : Y.obj) (a : target F G y) :
    (reverse F G y ⋙ forward F G y).obj a ≅ a :=
  CategoryTheory.CostructuredArrow.isoMk (Iso.refl a.left) (by sorry)

/-- The unit is natural in the original index. -/
theorem unitApp_naturality (y : Y.obj) {a b : source F G y} (k : a ⟶ b) :
    k ≫ (unitApp F G y b).hom =
      (unitApp F G y a).hom ≫ (forward F G y ⋙ reverse F G y).map k := sorry

/-- The counit is natural in the original index. -/
theorem counitApp_naturality (y : Y.obj) {a b : target F G y} (k : a ⟶ b) :
    (reverse F G y ⋙ forward F G y).map k ≫ (counitApp F G y b).hom =
      (counitApp F G y a).hom ≫ k := sorry

/-- Cartesian lifting gives the actual equivalence between the two base-change comma indices. -/
def equivalence (y : Y.obj) : source F G y ≌ target F G y where
  functor := forward F G y
  inverse := reverse F G y
  unitIso := NatIso.ofComponents (unitApp F G y)
    (fun k ↦ unitApp_naturality F G y k)
  counitIso := NatIso.ofComponents (counitApp F G y)
    (fun k ↦ counitApp_naturality F G y k)
  functor_unitIso_comp := sorry

/-- Forward index transport keeps the first object of the supplied pseudo-pullback index. -/
@[simp]
theorem forward_obj_left (y : Y.obj) (a : source F G y) :
    ((forward F G y).obj a).left = fstObj a.left := rfl

/-- Reverse index transport keeps the original first object; only the second side is pulled
back using the actual fibration input. -/
@[simp]
theorem reverse_obj_fst (y : Y.obj) (a : target F G y) :
    fstObj ((reverse F G y).obj a).left = a.left := rfl

/-- The first component of every reverse index map is the supplied original map. -/
@[simp]
theorem reverse_map_fst (y : Y.obj) {a b : target F G y} (k : a ⟶ b) :
    fstMap ((reverse F G y).map k).left = k.left := rfl

section Limits

universe uA vA
variable {A : Type uA} [Category.{vA} A]

/-- The original coefficient diagram on the comma index of the first functor. -/
abbrev targetDiagram (y : Y.obj) (P : X.objᵒᵖ ⥤ A) : (target F G y)ᵒᵖ ⥤ A :=
  (CategoryTheory.CostructuredArrow.proj F.toFunctor (G.obj y)).op ⋙ P

/-- The coefficient diagram on the pseudo-pullback comma index. -/
abbrev sourceDiagram (y : Y.obj) (P : X.objᵒᵖ ⥤ A) : (source F G y)ᵒᵖ ⥤ A :=
  (CategoryTheory.CostructuredArrow.proj (PseudoPullback.snd F G).toFunctor y).op ⋙
    (PseudoPullback.fst F G).toFunctor.op ⋙ P

/-- Forward index transport retains the actual first coefficient object and every first map. -/
def diagramIso (y : Y.obj) (P : X.objᵒᵖ ⥤ A) :
    (forward F G y).op ⋙ targetDiagram F G y P ≅ sourceDiagram F G y P :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; sorry)

/-- The given original limit supplies the base-changed one by the actual index equivalence,
followed by the specified coefficient comparison. -/
instance sourceDiagram_hasLimit (y : Y.obj) (P : X.objᵒᵖ ⥤ A)
    [Limits.HasLimit (targetDiagram F G y P)] : Limits.HasLimit (sourceDiagram F G y P) := by
  let e := (equivalence F G y).op
  letI : Limits.HasLimit ((forward F G y).op ⋙ targetDiagram F G y P) :=
    Limits.hasLimit_equivalence_comp e
  exact Limits.hasLimit_of_iso (diagramIso F G y P)

/-- Limits of the two actual base-change section diagrams have specified maps both ways.
The native initial-functor comparison is backed by the displayed index equivalence. -/
def limitIso (y : Y.obj) (P : X.objᵒᵖ ⥤ A)
    [Limits.HasLimit (targetDiagram F G y P)] :
    Limits.limit (sourceDiagram F G y P) ≅ Limits.limit (targetDiagram F G y P) := by
  let e := (equivalence F G y).op
  letI : Limits.HasLimit ((forward F G y).op ⋙ targetDiagram F G y P) :=
    Limits.hasLimit_equivalence_comp e
  exact (Limits.HasLimit.isoOfNatIso (diagramIso F G y P)).symm ≪≫
    (Limits.limit.isLimit ((forward F G y).op ⋙ targetDiagram F G y P)).conePointUniqueUpToIso
      ((Limits.limit.isLimit (targetDiagram F G y P)).whiskerEquivalence e)

/-- The forward limit map reads a section at the actual reverse comma index. Its first
coefficient object is the original one, so no additional coefficient transport is required. -/
theorem limitIso_hom_π (y : Y.obj) (P : X.objᵒᵖ ⥤ A)
    [Limits.HasLimit (targetDiagram F G y P)] (a : (target F G y)ᵒᵖ) :
    (limitIso F G y P).hom ≫ Limits.limit.π (targetDiagram F G y P) a =
      Limits.limit.π (sourceDiagram F G y P) (op ((reverse F G y).obj a.unop)) := sorry

/-- The reverse limit map simply reads the given family at the actual forward comma index. -/
theorem limitIso_inv_π (y : Y.obj) (P : X.objᵒᵖ ⥤ A)
    [Limits.HasLimit (targetDiagram F G y P)] (a : (source F G y)ᵒᵖ) :
    (limitIso F G y P).inv ≫ Limits.limit.π (sourceDiagram F G y P) a =
      Limits.limit.π (targetDiagram F G y P) (op ((forward F G y).obj a.unop)) := sorry

end Limits

end Reverse
end CategoryTheory.BasedCategory.PseudoPullback.CostructuredArrow
