/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.Cartesian
public import ReasLib.CategoryTheory.Sites.Simplicial.FaceDescent
public import ReasLib.CategoryTheory.Sites.Topos.Composition

/-!
# Coface descent for sheaves on a fiberwise simplicial site
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open CategoryTheory.SimplicialSites.Sheaf (vertexOp edgeOp)

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck.Sheaf

variable (C : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsFiberwiseSite C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable (A : Type (w + 1)) [Category.{w} A]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck A]
variable [HasWeakSheafify (topology C J) A]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj (op n))ᵒᵖ ⥤ A),
    (C.map φ.op).toFunctor.op.HasPointwiseRightKanExtension P]

/-- The sheafified inverse image is left adjoint to cocontinuous sheaf pushforward. -/
def inverseImageAdjunction {m n : SimplexCategory} (φ : m ⟶ n) :
    sheafInverseImage C J A φ ⊣
      (C.map φ.op).toFunctor.sheafPushforwardCocontinuous A
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck :=
  (((C.map φ.op).toFunctor.op.ranAdjunction A).comp
    (sheafificationAdjunction (J (op n)).toGrothendieck A)).restrictFullyFaithful
      (fullyFaithfulSheafToPresheaf (J (op m)).toGrothendieck A)
      (Functor.FullyFaithful.id _) (Iso.refl _)
      ((C.map φ.op).toFunctor.sheafPushforwardCocontinuousCompSheafToPresheafIso A
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck).symm

/-- Inverse image along a composite simplex operator identifies with successive inverse images. -/
def inverseImageCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    sheafInverseImage C J A (ψ ≫ φ) ≅
      sheafInverseImage C J A ψ ⋙ sheafInverseImage C J A φ :=
  (Adjunction.leftAdjointUniq
    (((inverseImageAdjunction C J A ψ).comp (inverseImageAdjunction C J A φ)).ofNatIsoRight
      (Functor.sheafPushforwardCocontinuousComp'
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck (J (op l)).toGrothendieck
        (C.map φ.op).toFunctor (C.map ψ.op).toFunctor (map_comp_toFunctor C ψ φ)))
    (inverseImageAdjunction C J A (ψ ≫ φ))).symm

/-- Equal simplex operators induce the same sheaf inverse image. -/
def recodeInverseImage {m n : SimplexCategory} {φ ψ : m ⟶ n} (h : φ = ψ) :
    sheafInverseImage C J A φ ≅ sheafInverseImage C J A ψ :=
  eqToIso (congrArg (fun t : m ⟶ n ↦ sheafInverseImage C J A t) h)

/-- Inverse image along an identity simplex operator identifies with the identity functor. -/
def inverseImageIdIso (n : SimplexCategory) :
    sheafInverseImage C J A (𝟙 n) ≅ 𝟭 (Sheaf (J (op n)).toGrothendieck A) :=
  let e :
      (Functor.whiskeringLeft (C.obj (op n))ᵒᵖ (C.obj (op n))ᵒᵖ A).obj
        (C.map (𝟙 n).op).toFunctor.op ≅ 𝟭 ((C.obj (op n))ᵒᵖ ⥤ A) :=
    (Functor.whiskeringLeft _ _ A).mapIso
        (NatIso.op (Cat.Hom.toNatIso (eqToIso (C.map_id (op n))))).symm ≪≫
      Functor.whiskeringLeftObjIdIso
  Functor.isoWhiskerLeft (sheafToPresheaf (J (op n)).toGrothendieck A)
      (Functor.isoWhiskerRight e (presheafToSheaf (J (op n)).toGrothendieck A) ≪≫
        Functor.leftUnitor _) ≪≫
    (sheafificationNatIso (J (op n)).toGrothendieck A).symm

/-- The pullback of `α` along a 2-face `δ i`, as a morphism of sheaves on `C_2`. -/
def facePullback (i : Fin 3) {F : Sheaf ((J (op ⦋0⦌)).toGrothendieck) A}
    (α : (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj F) :
    (sheafInverseImage C J A
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ i)).obj F ⟶
      (sheafInverseImage C J A
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ i)).obj F :=
  (inverseImageCompIso C J A (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ i)).hom.app
      F ≫
    (sheafInverseImage C J A (SimplexCategory.δ i)).map α.hom ≫
    (inverseImageCompIso C J A (SimplexCategory.δ (0 : Fin 2))
        (SimplexCategory.δ i)).inv.app F

/-- `(f_{δ 1})⁻¹ α` transported to a morphism out of `(f_{δ 1 ≫ δ 2})⁻¹ F`. -/
def cocycleLeft {F : Sheaf ((J (op ⦋0⦌)).toGrothendieck) A}
    (α : (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj F) :
    (sheafInverseImage C J A
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).obj F ⟶
      (sheafInverseImage C J A
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).obj F :=
  (recodeInverseImage C J A
        (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app F ≫
    facePullback C J A 1 α

/-- `(f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α` after the `δ_comp_δ` identifications on `C_2`. -/
def cocycleRight {F : Sheaf ((J (op ⦋0⦌)).toGrothendieck) A}
    (α : (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj F) :
    (sheafInverseImage C J A
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).obj F ⟶
      (sheafInverseImage C J A
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).obj F :=
  facePullback C J A 2 α ≫
    (recodeInverseImage C J A
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (Fin.zero_le _))).hom.app F ≫
    facePullback C J A 0 α ≫
    (recodeInverseImage C J A
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
          le_rfl).symm).hom.app F

/-- A pair `(F, α)` with `F` a sheaf on `C_0` and `α : (f_{δ 1})⁻¹ F ≅ (f_{δ 0})⁻¹ F` on
`C_1` satisfying the `C_2` cocycle `(f_{δ 1})⁻¹ α = (f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α`. -/
structure FaceDescent.Obj where
  /-- The sheaf `F` on `C_0`. -/
  sheaf : Sheaf ((J (op ⦋0⦌)).toGrothendieck) A
  /-- The isomorphism `α : (f_{δ 1})⁻¹ F ≅ (f_{δ 0})⁻¹ F` of sheaves on `C_1`. -/
  iso :
    (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj sheaf ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj sheaf
  /-- The cocycle `(f_{δ 1})⁻¹ α = (f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α` on `C_2`. -/
  cocycle : cocycleLeft C J A iso = cocycleRight C J A iso

namespace FaceDescent

variable {C J A}

/-- Build face-descent data from a sheaf on `C_0`, a coface isomorphism on `C_1`, and the
cocycle proof. -/
def ofIso (F : Sheaf ((J (op ⦋0⦌)).toGrothendieck) A)
    (α : (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).obj F)
    (hcocycle : cocycleLeft C J A α = cocycleRight C J A α) :
    Obj C J A where
  sheaf := F
  iso := α
  cocycle := hcocycle

/-- The coface comparison is invertible and satisfies the degree-two cocycle. -/
theorem spec (D : Obj C J A) :
    IsIso D.iso.hom ∧ cocycleLeft C J A D.iso = cocycleRight C J A D.iso :=
  sorry

/-- A morphism of face-descent pairs is a map of the underlying sheaves on `C_0` commuting
with `α`. -/
structure Hom (D E : Obj C J A) where
  /-- The underlying morphism of sheaves on `C_0`. -/
  hom : D.sheaf ⟶ E.sheaf
  /-- Commutation with the coface isomorphisms on `C_1`. -/
  comm :
    (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).map hom ≫ E.iso.hom =
      D.iso.hom ≫ (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).map hom

/-- Build a morphism of face-descent pairs from a sheaf map commuting with `α`. -/
def homMk {D E : Obj C J A} (f : D.sheaf ⟶ E.sheaf)
    (comm :
      (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).map f ≫ E.iso.hom =
        D.iso.hom ≫ (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).map f) :
    Hom D E where
  hom := f
  comm := comm

/-- The morphism constructor has the prescribed underlying map and commutes with
both coface inverse images. -/
theorem homMk_spec {D E : Obj C J A} (f : D.sheaf ⟶ E.sheaf)
    (comm :
      (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).map f ≫ E.iso.hom =
      D.iso.hom ≫ (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).map f) :
    (homMk f comm).hom = f ∧
      (sheafInverseImage C J A (SimplexCategory.δ (1 : Fin 2))).map (homMk f comm).hom ≫ E.iso.hom =
      D.iso.hom ≫ (sheafInverseImage C J A (SimplexCategory.δ (0 : Fin 2))).map (homMk f comm).hom := sorry

/-- The identity morphism of face-descent pairs. -/
def Hom.id (D : Obj C J A) : Hom D D :=
  homMk (𝟙 D.sheaf) sorry

/-- Composition of morphisms of face-descent pairs. -/
def Hom.comp {D E F : Obj C J A} (f : Hom D E) (g : Hom E F) : Hom D F :=
  homMk (f.hom ≫ g.hom) sorry

/-- The explicit category structure on coface descent objects. -/
@[reducible]
def categoryData : Category (Obj C J A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end FaceDescent

/-- The bundled category of degree-zero sheaves with an invertible coface comparison
satisfying the degree-two cocycle. -/
def FaceDescent : Cat :=
  ⟨FaceDescent.Obj C J A, FaceDescent.categoryData⟩

namespace FaceDescent

variable {C J A}

/-- The reconstructed comparison `G(φ) : (f_φ)⁻¹ G_n ⟶ G_m` attached to a pair `(F, α)`. -/
def transitionOf {n m : SimplexCategory} (φ : n ⟶ m) (D : FaceDescent C J A) :
    (sheafInverseImage C J A φ).obj
        ((sheafInverseImage C J A (vertexOp n)).obj D.sheaf) ⟶
      (sheafInverseImage C J A (vertexOp m)).obj D.sheaf :=
  (inverseImageCompIso C J A (vertexOp n) φ).inv.app D.sheaf ≫
    (recodeInverseImage C J A
        (SimplexCategory.Hom.ext_zero_left (vertexOp n ≫ φ)
          (SimplexCategory.δ (1 : Fin 2) ≫ edgeOp φ))).hom.app D.sheaf ≫
    (inverseImageCompIso C J A (SimplexCategory.δ (1 : Fin 2)) (edgeOp φ)).hom.app
      D.sheaf ≫
    (sheafInverseImage C J A (edgeOp φ)).map D.iso.hom ≫
    (inverseImageCompIso C J A (SimplexCategory.δ (0 : Fin 2)) (edgeOp φ)).inv.app
      D.sheaf ≫
    (recodeInverseImage C J A
        (SimplexCategory.Hom.ext_zero_left
          (SimplexCategory.δ (0 : Fin 2) ≫ edgeOp φ) (vertexOp m))).hom.app D.sheaf

end FaceDescent

attribute [instance] cartesian_isCartesian

/-- Extract the pair `(F_0, α)` from a cartesian sheaf, with
`α = F(δ 1) ≪≫ F(δ 0).symm`. -/
def toDescent (F : Cartesian C J A) : FaceDescent C J A :=
  FaceDescent.ofIso ((fiberRestrict C J A ⦋0⦌).obj F.obj)
    (transitionIso C J A F.obj (SimplexCategory.δ (1 : Fin 2)) ≪≫
      (transitionIso C J A F.obj (SimplexCategory.δ (0 : Fin 2))).symm)
    sorry

/-- The sheaf on `C_0` extracted by `toDescent` is the degree-zero component. -/
theorem toDescent_sheaf (F : Cartesian C J A) :
    (toDescent C J A F).sheaf = (fiberRestrict C J A ⦋0⦌).obj F.obj :=
  sorry

/-- Restriction along a total-category arrow uses its fiber map, the sheafification
unit, and the last-vertex transition. -/
def ofDescentPresheafMap (D : FaceDescent C J A) {U V : Grothendieck C} (η : U ⟶ V) :
    ((sheafInverseImage C J A (vertexOp V.base.unop)).obj D.sheaf).obj.obj (op V.fiber) ⟶
      ((sheafInverseImage C J A (vertexOp U.base.unop)).obj D.sheaf).obj.obj (op U.fiber) :=
  let Gm := (sheafInverseImage C J A (vertexOp V.base.unop)).obj D.sheaf
  let P := (C.map η.base).toFunctor.op ⋙ Gm.obj
  Gm.obj.map η.fiber.op ≫
    ((sheafificationAdjunction (J U.base).toGrothendieck A).unit.app P).app (op U.fiber) ≫
    (FaceDescent.transitionOf η.base.unop D).hom.app (op U.fiber)

/-- The assembled presheaf on `C_total` associated to a pair `(F, α)`: value at `U` is
`(f_{τ^{deg U}_{deg U}})⁻¹ F` at `U.fiber`. -/
def ofDescentPresheaf (D : FaceDescent C J A) : (Grothendieck C)ᵒᵖ ⥤ A where
  obj W :=
    ((sheafInverseImage C J A (vertexOp (W.unop.base.unop))).obj D.sheaf).obj.obj
      (op (W.unop.fiber))
  map {W Z} η := ofDescentPresheafMap C J A D η.unop
  map_id := sorry
  map_comp := sorry

/-- Assemble a sheaf on `C_total` from a face-descent pair. -/
def ofDescent (D : FaceDescent C J A) : Sheaf (topology C J) A :=
  ⟨ofDescentPresheaf C J A D, sorry⟩

/-- Sections of `ofDescent D` over `U` are the sections of `(f_{τ^{deg U}_{deg U}})⁻¹ F`
over `U.fiber`. -/
theorem ofDescent_obj_app (D : FaceDescent C J A) (U : Grothendieck C) :
    (ofDescent C J A D).obj.obj (op U) =
      ((sheafInverseImage C J A (vertexOp (U.base.unop))).obj D.sheaf).obj.obj (op (U.fiber)) :=
  sorry

/-- The sheaf morphism on `C_total` induced by a morphism of face-descent pairs. -/
def ofDescentMap {D E : FaceDescent C J A} (α : FaceDescent.Hom D E) :
    ofDescent C J A D ⟶ ofDescent C J A E :=
  ObjectProperty.homMk
    { app := fun W ↦
        ((sheafInverseImage C J A (vertexOp (W.unop.base.unop))).map α.hom).hom.app
          (op (W.unop.fiber))
      naturality := sorry }

/-- The functor sending a cartesian sheaf to the extracted pair `(F_0, α)`. -/
def toDescentFunctor : Cartesian C J A ⥤ FaceDescent C J A where
  obj F := toDescent C J A F
  map {F G} f := FaceDescent.homMk ((fiberRestrict C J A ⦋0⦌).map f.hom) sorry
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- The functor assembling a cartesian sheaf on `C_total` from a face-descent pair. -/
def ofDescentFunctor : FaceDescent C J A ⥤ Cartesian C J A where
  obj D := ⟨ofDescent C J A D, sorry⟩
  map {D E} α := ObjectProperty.homMk (ofDescentMap C J A α)
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- Component of the unit isomorphism on underlying presheaves. -/
def cartesianUnitPresheaf (F : Cartesian C J A) :
    F.obj.obj ⟶ (ofDescent C J A (toDescent C J A F)).obj where
  app W :=
    ((ι C (op W.unop.base.unop)).sheafPushforwardContinuousObjObjIso A F.obj W.unop.fiber).inv ≫
      (transitionIso C J A F.obj (vertexOp (W.unop.base.unop))).inv.hom.app
        (op (W.unop.fiber))
  naturality := sorry

/-- Component of the inverse unit isomorphism on underlying presheaves. -/
def cartesianUnitPresheafInv (F : Cartesian C J A) :
    (ofDescent C J A (toDescent C J A F)).obj ⟶ F.obj.obj where
  app W :=
    (transitionIso C J A F.obj (vertexOp (W.unop.base.unop))).hom.hom.app
        (op (W.unop.fiber)) ≫
      ((ι C (op W.unop.base.unop)).sheafPushforwardContinuousObjObjIso A F.obj W.unop.fiber).hom
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
    (fiberRestrict C J A ⦋0⦌).obj (ofDescent C J A D) ≅
      (sheafInverseImage C J A (vertexOp ⦋0⦌)).obj D.sheaf :=
  { hom := ObjectProperty.homMk
      { app := fun V ↦ ((ι C (op ⦋0⦌)).sheafPushforwardContinuousObjObjIso A (ofDescent C J A D) V.unop).hom
        naturality := sorry }
    inv := ObjectProperty.homMk
      { app := fun V ↦ ((ι C (op ⦋0⦌)).sheafPushforwardContinuousObjObjIso A (ofDescent C J A D) V.unop).inv
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

end CategoryTheory.Grothendieck.Sheaf
