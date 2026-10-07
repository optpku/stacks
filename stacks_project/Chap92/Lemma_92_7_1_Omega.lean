module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Kaehler.Basic
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver

/-!
# Naive Kähler sheaves on the polynomial site

This leaf owns the sheaf of naive differentials `Ω_{O/A} ⊗_O underline{B}` on `C_{B/A}`,
as a functor `(PolynomialSite A B)ᵒᵖ ⥤ ModuleCat B`.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped TensorProduct

noncomputable section

universe u

namespace CommAlgCat.Over.Polynomial.Site

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The algebra structure on `B` induced by a polynomial arrow `P ⟶ B`. -/
@[reducible] def algebraToBase (X : Algebra.PolynomialOver A B) : Algebra X.obj.left B :=
  RingHom.toAlgebra X.obj.hom.hom.toRingHom

/-- Unfolding `algebraToBase` recovers the structure morphism of the polynomial arrow. -/
theorem algebraToBase_eq (X : Algebra.PolynomialOver A B) :
    algebraToBase X = RingHom.toAlgebra X.obj.hom.hom.toRingHom :=
  sorry

/-- The `P`-algebra structure on `P'` induced by a morphism of polynomial arrows. -/
@[reducible] def algebraOfHom {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    Algebra X.obj.left Y.obj.left :=
  RingHom.toAlgebra f.hom.left.hom.toRingHom

/-- Unfolding `algebraOfHom` recovers the underlying ring map of the morphism. -/
theorem algebraOfHom_eq {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    algebraOfHom f = RingHom.toAlgebra f.hom.left.hom.toRingHom :=
  sorry

/-- The tower `A ⟶ P ⟶ P'` of a morphism of polynomial arrows. -/
theorem isScalarTower_algebraOfHom {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left Y.obj.left] :
    IsScalarTower A X.obj.left Y.obj.left :=
  sorry

/-- The structure morphisms of a polynomial-arrow morphism compose over `B`. -/
theorem toBase_comp {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    Y.obj.hom.hom.toRingHom.comp f.hom.left.hom.toRingHom = X.obj.hom.hom.toRingHom :=
  congrArg (fun g : X.obj.left ⟶ CommAlgCat.of A B ↦ g.hom.toRingHom) f.hom.w

/-- The tower `P ⟶ P' ⟶ B` of a morphism of polynomial arrows over `B`. -/
theorem isScalarTower_toBase {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left Y.obj.left] [Algebra Y.obj.left B] [Algebra X.obj.left B] :
    IsScalarTower X.obj.left Y.obj.left B :=
  sorry

/-- The naive differentials of a polynomial arrow `P ⟶ B`, as the `B`-module
`Ω[P ⁄ A] ⊗[P] B`, in the presence of the induced `P`-algebra structure on `B`. -/
def omegaSheafObjWith (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    ModuleCat.{u} B :=
  ModuleCat.of B (B ⊗[X.obj.left] KaehlerDifferential A X.obj.left)

/-- The naive differentials of a polynomial arrow `P ⟶ B`, as the `B`-module
`Ω[P ⁄ A] ⊗[P] B`. -/
def omegaSheafObj (X : Algebra.PolynomialOver A B) : ModuleCat.{u} B :=
  @omegaSheafObjWith A B _ _ _ X (algebraToBase X)

/-- Unfolding `omegaSheafObj` recovers the unbundled tensor of Kähler differentials. -/
theorem omegaSheafObj_eq (X : Algebra.PolynomialOver A B) :
    omegaSheafObj X = @omegaSheafObjWith A B _ _ _ X (algebraToBase X) :=
  sorry

/-- The map on naive differentials induced by a morphism of polynomial arrows, in the
presence of the induced algebra structures. -/
def omegaSheafMapWith {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left B] [Algebra Y.obj.left B]
    [Algebra X.obj.left Y.obj.left]
    [IsScalarTower A X.obj.left Y.obj.left]
    [IsScalarTower X.obj.left Y.obj.left B] :
    omegaSheafObjWith X ⟶ omegaSheafObjWith Y :=
  ModuleCat.ofHom
    ((KaehlerDifferential.mapBaseChange A X.obj.left Y.obj.left).baseChange B ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        X.obj.left Y.obj.left B B (KaehlerDifferential A X.obj.left)).symm.toLinearMap)

/-- The map on naive differentials induced by a morphism of polynomial arrows over `B`. -/
def omegaSheafMap {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    omegaSheafObj X ⟶ omegaSheafObj Y :=
  @omegaSheafMapWith A B _ _ _ X Y f (algebraToBase X) (algebraToBase Y) (algebraOfHom f)
    (@isScalarTower_algebraOfHom A B _ _ _ X Y f (algebraOfHom f))
    (@isScalarTower_toBase A B _ _ _ X Y f (algebraOfHom f) (algebraToBase Y) (algebraToBase X))

/-- Unfolding `omegaSheafMap` recovers the base-change of `KaehlerDifferential.mapBaseChange`. -/
theorem omegaSheafMap_eq {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    omegaSheafMap f =
      @omegaSheafMapWith A B _ _ _ X Y f (algebraToBase X) (algebraToBase Y) (algebraOfHom f)
        (@isScalarTower_algebraOfHom A B _ _ _ X Y f (algebraOfHom f))
        (@isScalarTower_toBase A B _ _ _ X Y f (algebraOfHom f) (algebraToBase Y)
          (algebraToBase X)) :=
  sorry

/-- Identity morphisms act as the identity on naive differentials. -/
theorem omegaSheafMap_id (X : Algebra.PolynomialOver A B) :
    omegaSheafMap (𝟙 X) = 𝟙 (omegaSheafObj X) :=
  sorry

/-- Composition of polynomial-arrow morphisms maps to composition of naive differentials. -/
theorem omegaSheafMap_comp {X Y Z : Algebra.PolynomialOver A B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    omegaSheafMap (f ≫ g) = omegaSheafMap f ≫ omegaSheafMap g :=
  sorry

variable (A B) in
/-- The covariant functor of naive differentials on polynomial arrows `P ⟶ B`. -/
def omegaSheafCov : Algebra.PolynomialOver A B ⥤ ModuleCat.{u} B where
  obj := omegaSheafObj
  map f := omegaSheafMap f
  map_id X := omegaSheafMap_id X
  map_comp f g := omegaSheafMap_comp f g

/-- Objects of `omegaSheafCov` are the naive differentials of the corresponding polynomial
arrow. -/
theorem omegaSheafCov_obj (X : Algebra.PolynomialOver A B) :
    (omegaSheafCov A B).obj X = omegaSheafObj X :=
  sorry

variable (A B) in
/-- The sheaf `Ω_{O/A} ⊗_O underline{B}` on `C_{B/A}`, as a functor
`(PolynomialSite A B)ᵒᵖ ⥤ ModuleCat B`. -/
def omegaSheaf : (Algebra.PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B :=
  unopUnop (Algebra.PolynomialOver A B) ⋙ omegaSheafCov A B

/-- Evaluating `omegaSheaf` on a double-opposite polynomial arrow recovers `omegaSheafObj`. -/
theorem omegaSheaf_obj (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (omegaSheaf A B).obj X = omegaSheafObj (unop (unop X)) :=
  sorry

/-- `omegaSheaf` is precomposition of `omegaSheafCov` with the double-opposite equivalence. -/
theorem omegaSheaf_eq :
    omegaSheaf A B = unopUnop (Algebra.PolynomialOver A B) ⋙ omegaSheafCov A B :=
  sorry

/-- Components of `omegaSheaf` on morphisms are `omegaSheafMap` of the underlying polynomial
arrow. -/
theorem omegaSheaf_map {X Y : (Algebra.PolynomialSite A B)ᵒᵖ} (f : X ⟶ Y) :
    (omegaSheaf A B).map f = omegaSheafMap f.unop.unop :=
  sorry

end CommAlgCat.Over.Polynomial.Site
