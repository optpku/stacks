/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap85.Lemma_85_12_4_Descent

/-!
# Equivalence between cartesian sheaves and face-descent data

Cartesian sheaves on `C_total` are equivalent to pairs `(F, α)` on `C_0` and `C_1`
satisfying the `C_2` cocycle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.Sheaf

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable (A : Type (w + 1)) [Category.{w} A]
variable [instWeakSheafifyA : ∀ n, HasWeakSheafify (J n).toGrothendieck A]
variable [instLeftKanA : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ A),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan instWeakSheafifyA instLeftKanA

/-- The object property of being a cartesian sheaf on `C_total`. -/
abbrev cartesianProperty : ObjectProperty (Sheaf (topology C J) A) :=
  fun F ↦ IsCartesian C J F

/-- The category of cartesian sheaves on `C_total` with coefficients in `A`. -/
abbrev Cartesian := (cartesianProperty C J A).FullSubcategory

/-- The structure morphism of a cartesian sheaf is cartesian. -/
theorem cartesian_isCartesian (F : Cartesian C J A) : IsCartesian C J F.obj :=
  sorry

/-- The isomorphism `F(φ) : f_φ⁻¹ F_m ≅ F_n` extracted from a cartesianness proof. -/
def cartesianFaceIso (F : Sheaf (topology C J) A) (h : IsCartesian C J F)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (sheafInverseImage C J A φ).obj ((component C J A m).obj F) ≅
      (component C J A n).obj F :=
  @asIso _ _ _ _ (sheafTransition C J A φ F) (h.isIso_transition φ)

/-- The forward map of `cartesianFaceIso` is `sheafTransition`. -/
theorem cartesianFaceIso_hom (F : Sheaf (topology C J) A) (h : IsCartesian C J F)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (cartesianFaceIso C J A F h φ).hom = sheafTransition C J A φ F :=
  sorry

/-- Extract the pair `(F_0, α)` from a cartesian sheaf, with
`α = F(δ 1) ≪≫ F(δ 0).symm`. -/
def toDescent (F : Cartesian C J A) : FaceDescent C J A :=
  FaceDescent.ofIso ((component C J A ⦋0⦌).obj F.obj)
    (cartesianFaceIso C J A F.obj F.property (SimplexCategory.δ (1 : Fin 2)) ≪≫
      (cartesianFaceIso C J A F.obj F.property (SimplexCategory.δ (0 : Fin 2))).symm)
    sorry

/-- The sheaf on `C_0` extracted by `toDescent` is the degree-zero component. -/
theorem toDescent_sheaf (F : Cartesian C J A) :
    (toDescent C J A F).sheaf = (component C J A ⦋0⦌).obj F.obj :=
  sorry

/-- Restriction of a reconstructed sheaf along a total-category morphism `(φ, g)`. -/
def ofDescentPresheafMap (D : FaceDescent C J A) {U V : totalSite C} (η : U ⟶ V) :
    ((sheafInverseImage C J A (vertexOp (degree V))).obj D.sheaf).obj.obj (op (obj V)) ⟶
      ((sheafInverseImage C J A (vertexOp (degree U))).obj D.sheaf).obj.obj (op (obj U)) :=
  ((((C.map (homToPair η).1).toFunctor.sheafAdjunctionContinuous A
          (J (degree V)).toGrothendieck (J (degree U)).toGrothendieck).homEquiv
        ((sheafInverseImage C J A (vertexOp (degree V))).obj D.sheaf)
        ((sheafInverseImage C J A (vertexOp (degree U))).obj D.sheaf))
      (FaceDescent.transitionOf (homToPair η).1 D)).hom.app (op (obj V)) ≫
    (Functor.sheafPushforwardContinuousObjObjIso (C.map (homToPair η).1).toFunctor A
      ((sheafInverseImage C J A (vertexOp (degree U))).obj D.sheaf) (obj V)).hom ≫
    ((sheafInverseImage C J A (vertexOp (degree U))).obj D.sheaf).obj.map (homToPair η).2.op

/-- The assembled presheaf on `C_total` associated to a pair `(F, α)`: value at `U` is
`(f_{τ^{deg U}_{deg U}})⁻¹ F` at `obj U`. -/
def ofDescentPresheaf (D : FaceDescent C J A) : (totalSite C)ᵒᵖ ⥤ A where
  obj W :=
    ((sheafInverseImage C J A (vertexOp (degree W.unop))).obj D.sheaf).obj.obj
      (op (obj W.unop))
  map {W Z} η := ofDescentPresheafMap C J A D η.unop
  map_id := sorry
  map_comp := sorry

/-- Assemble a sheaf on `C_total` from a face-descent pair. -/
def ofDescent (D : FaceDescent C J A) : Sheaf (topology C J) A :=
  ⟨ofDescentPresheaf C J A D, sorry⟩

/-- Sections of `ofDescent D` over `U` are the sections of `(f_{τ^{deg U}_{deg U}})⁻¹ F`
over `obj U`. -/
theorem ofDescent_obj_app (D : FaceDescent C J A) (U : totalSite C) :
    (ofDescent C J A D).obj.obj (op U) =
      ((sheafInverseImage C J A (vertexOp (degree U))).obj D.sheaf).obj.obj (op (obj U)) :=
  sorry

/-- The sheaf morphism on `C_total` induced by a morphism of face-descent pairs. -/
def ofDescentMap {D E : FaceDescent C J A} (α : FaceDescent.Hom D E) :
    ofDescent C J A D ⟶ ofDescent C J A E :=
  ObjectProperty.homMk
    { app := fun W ↦
        ((sheafInverseImage C J A (vertexOp (degree W.unop))).map α.hom).hom.app
          (op (obj W.unop))
      naturality := sorry }

/-- The functor sending a cartesian sheaf to the extracted pair `(F_0, α)`. -/
def toDescentFunctor : Cartesian C J A ⥤ FaceDescent C J A where
  obj F := toDescent C J A F
  map {F G} f := FaceDescent.homMk ((component C J A ⦋0⦌).map f.hom) sorry
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- On objects, `toDescentFunctor` is `toDescent`. -/
theorem toDescentFunctor_obj (F : Cartesian C J A) :
    (toDescentFunctor C J A).obj F = toDescent C J A F :=
  sorry

/-- The functor assembling a cartesian sheaf on `C_total` from a face-descent pair. -/
def ofDescentFunctor : FaceDescent C J A ⥤ Cartesian C J A where
  obj D := ⟨ofDescent C J A D, sorry⟩
  map {D E} α := ObjectProperty.homMk (ofDescentMap C J A α)
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- On objects, the underlying sheaf of `ofDescentFunctor` is `ofDescent`. -/
theorem ofDescentFunctor_obj_obj (D : FaceDescent C J A) :
    ((ofDescentFunctor C J A).obj D).obj = ofDescent C J A D :=
  sorry

/-- Component of the unit isomorphism on underlying presheaves. -/
def cartesianUnitPresheaf (F : Cartesian C J A) :
    F.obj.obj ⟶ (ofDescent C J A (toDescent C J A F)).obj where
  app W :=
    (component_obj C J A (degree W.unop) F.obj (obj W.unop)).inv ≫
      (cartesianFaceIso C J A F.obj F.property (vertexOp (degree W.unop))).inv.hom.app
        (op (obj W.unop))
  naturality := sorry

/-- Component of the inverse unit isomorphism on underlying presheaves. -/
def cartesianUnitPresheafInv (F : Cartesian C J A) :
    (ofDescent C J A (toDescent C J A F)).obj ⟶ F.obj.obj where
  app W :=
    (cartesianFaceIso C J A F.obj F.property (vertexOp (degree W.unop))).hom.hom.app
        (op (obj W.unop)) ≫
      (component_obj C J A (degree W.unop) F.obj (obj W.unop)).hom
  naturality := sorry

/-- The unit isomorphism on underlying sheaves of the cartesian / face-descent equivalence. -/
def cartesianUnitSheafIso (F : Cartesian C J A) :
    F.obj ≅ ofDescent C J A (toDescent C J A F) :=
  { hom := ObjectProperty.homMk (cartesianUnitPresheaf C J A F)
    inv := ObjectProperty.homMk (cartesianUnitPresheafInv C J A F)
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The unit isomorphism of the cartesian / face-descent equivalence, at an object `F`. -/
def cartesianUnitApp (F : Cartesian C J A) :
    F ≅ (ofDescentFunctor C J A).obj ((toDescentFunctor C J A).obj F) :=
  (cartesianProperty C J A).isoMk (cartesianUnitSheafIso C J A F)

/-- The unit natural isomorphism `𝟭 ≅ toDescentFunctor ⋙ ofDescentFunctor`. -/
def cartesianUnitIso :
    𝟭 (Cartesian C J A) ≅ toDescentFunctor C J A ⋙ ofDescentFunctor C J A :=
  NatIso.ofComponents (fun F ↦ cartesianUnitApp C J A F) sorry

/-- Comparison of the degree-zero restriction of `ofDescent D` with `(f_{τ^0_0})⁻¹ F`. -/
def ofDescentComponentZeroIso (D : FaceDescent C J A) :
    (component C J A ⦋0⦌).obj (ofDescent C J A D) ≅
      (sheafInverseImage C J A (vertexOp ⦋0⦌)).obj D.sheaf :=
  { hom := ObjectProperty.homMk
      { app := fun V ↦ (component_obj C J A ⦋0⦌ (ofDescent C J A D) V.unop).hom
        naturality := sorry }
    inv := ObjectProperty.homMk
      { app := fun V ↦ (component_obj C J A ⦋0⦌ (ofDescent C J A D) V.unop).inv
        naturality := sorry }
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Identification of `(f_{τ^0_0})⁻¹ F` with `F` via `τ^0_0 = id`. -/
def vertexOpZeroIso (D : FaceDescent C J A) :
    (sheafInverseImage C J A (vertexOp ⦋0⦌)).obj D.sheaf ≅ D.sheaf :=
  (recodeInverseImage C J A SimplexCategory.const_eq_id).app D.sheaf ≪≫
    (inverseImageIdIso C J A ⦋0⦌).app D.sheaf

/-- The counit isomorphism of the cartesian / face-descent equivalence, at a pair `D`. -/
def cartesianCounitApp (D : FaceDescent C J A) :
    (toDescentFunctor C J A).obj ((ofDescentFunctor C J A).obj D) ≅ D :=
  { hom :=
      FaceDescent.homMk
        ((ofDescentComponentZeroIso C J A D).hom ≫ (vertexOpZeroIso C J A D).hom) sorry
    inv :=
      FaceDescent.homMk
        ((vertexOpZeroIso C J A D).inv ≫ (ofDescentComponentZeroIso C J A D).inv) sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The counit natural isomorphism `ofDescentFunctor ⋙ toDescentFunctor ≅ 𝟭`. -/
def cartesianCounitIso :
    ofDescentFunctor C J A ⋙ toDescentFunctor C J A ≅ 𝟭 (FaceDescent C J A) :=
  NatIso.ofComponents (fun D ↦ cartesianCounitApp C J A D) sorry

/-- Cartesian sheaves on `C_total` with coefficients in `A` are equivalent to face-descent
pairs `(F, α)`. -/
def cartesianEquivalence : Cartesian C J A ≌ FaceDescent C J A :=
  Equivalence.mk (toDescentFunctor C J A) (ofDescentFunctor C J A)
    (cartesianUnitIso C J A) (cartesianCounitIso C J A)

/-- The forward functor of `cartesianEquivalence` extracts the pair `(F_0, α)`. -/
theorem cartesianEquivalence_functor :
    (cartesianEquivalence C J A).functor = toDescentFunctor C J A :=
  sorry

/-- The inverse functor of `cartesianEquivalence` assembles a cartesian sheaf from a pair
`(F, α)`. -/
theorem cartesianEquivalence_inverse :
    (cartesianEquivalence C J A).inverse = ofDescentFunctor C J A :=
  sorry

end CategoryTheory.SimplicialSites.Sheaf
