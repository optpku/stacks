/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite
public import ReasLib.RingTheory.Kaehler.BaseChange

/-!
# Differentials on the polynomial site

Scalar extension of Kähler differentials is functorial on augmented polynomial algebras.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped TensorProduct

noncomputable section

universe u

namespace CommAlgCat.Over.Polynomial.Site

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The augmentation makes the target an algebra over the polynomial source. -/
@[reducible] def algebraToBase (X : Algebra.PolynomialOver A B) : Algebra X.obj.left B :=
  RingHom.toAlgebra X.obj.hom.hom.toRingHom

/-- A morphism of augmented polynomial algebras induces an algebra structure on its target. -/
@[reducible] def algebraOfHom {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    Algebra X.obj.left Y.obj.left :=
  RingHom.toAlgebra f.hom.left.hom.toRingHom

/-- The algebra structure induced by an algebra morphism respects the original base. -/
instance algebraOfHom_isScalarTower {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    @IsScalarTower A X.obj.left Y.obj.left _ (algebraOfHom f).toSMul _ :=
  IsScalarTower.of_algHom f.hom.left.hom

/-- Augmentations commute with morphisms of augmented polynomial algebras. -/
theorem toBase_comp {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    Y.obj.hom.hom.toRingHom.comp f.hom.left.hom.toRingHom = X.obj.hom.hom.toRingHom :=
  congrArg (fun g : X.obj.left ⟶ CommAlgCat.of A B ↦ g.hom.toRingHom) f.hom.w

/-- The morphism-induced and augmentation-induced algebra structures form a scalar tower. -/
instance toBase_isScalarTower {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    @IsScalarTower X.obj.left Y.obj.left B (algebraOfHom f).toSMul
      (algebraToBase Y).toSMul (algebraToBase X).toSMul :=
  @IsScalarTower.of_algebraMap_eq X.obj.left Y.obj.left B _ _ _
    (algebraOfHom f) (algebraToBase Y) (algebraToBase X)
    (fun x ↦ (RingHom.congr_fun (toBase_comp f) x).symm)

/-- Differentials of an augmented polynomial algebra, extended along a specified algebra action. -/
def omegaSheafObjWith (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    ModuleCat.{u} B :=
  ModuleCat.of B (B ⊗[X.obj.left] KaehlerDifferential A X.obj.left)

/-- Differentials of an augmented polynomial algebra, extended along its augmentation. -/
def omegaSheafObj (X : Algebra.PolynomialOver A B) : ModuleCat.{u} B :=
  @omegaSheafObjWith A B _ _ _ X (algebraToBase X)

/-- Compatible algebra actions induce a map on scalar-extended differentials. -/
def omegaSheafMapWith {X Y : Algebra.PolynomialOver A B} (_f : X ⟶ Y)
    [Algebra X.obj.left B] [Algebra Y.obj.left B]
    [Algebra X.obj.left Y.obj.left]
    [IsScalarTower A X.obj.left Y.obj.left]
    [IsScalarTower X.obj.left Y.obj.left B] :
    omegaSheafObjWith X ⟶ omegaSheafObjWith Y :=
  ModuleCat.ofHom (KaehlerDifferential.tensorMapBaseChange A X.obj.left Y.obj.left B)

/-- A morphism of augmented polynomial algebras induces a map on extended differentials. -/
def omegaSheafMap {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    omegaSheafObj X ⟶ omegaSheafObj Y :=
  @omegaSheafMapWith A B _ _ _ X Y f (algebraToBase X) (algebraToBase Y) (algebraOfHom f)
    (algebraOfHom_isScalarTower f) (toBase_isScalarTower f)

/-- The induced map sends the differential of an element to the differential of its image. -/
theorem omegaSheafMap_tmul_D {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    (b : B) (x : X.obj.left) :
    (omegaSheafMap f).hom
      (@TensorProduct.tmul X.obj.left _ B (KaehlerDifferential A X.obj.left) _ _ (algebraToBase X).toModule _
        b (KaehlerDifferential.D A X.obj.left x)) =
      @TensorProduct.tmul Y.obj.left _ B (KaehlerDifferential A Y.obj.left) _ _ (algebraToBase Y).toModule _
        b (KaehlerDifferential.D A Y.obj.left (f.hom.left x)) := by
  sorry

/-- Identity morphisms act identically on extended differentials. -/
theorem omegaSheafMap_id (X : Algebra.PolynomialOver A B) :
    omegaSheafMap (𝟙 X) = 𝟙 (omegaSheafObj X) := by
  sorry

/-- Extended differentials preserve composition of morphisms of augmented polynomial algebras. -/
theorem omegaSheafMap_comp {X Y Z : Algebra.PolynomialOver A B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    omegaSheafMap (f ≫ g) = omegaSheafMap f ≫ omegaSheafMap g := by
  sorry

variable (A B) in
/-- The covariant functor of scalar-extended differentials on augmented polynomial algebras. -/
def omegaSheafCov : Algebra.PolynomialOver A B ⥤ ModuleCat.{u} B where
  obj := omegaSheafObj
  map f := omegaSheafMap f
  map_id X := omegaSheafMap_id X
  map_comp f g := omegaSheafMap_comp f g

variable (A B) in
/-- The presheaf of scalar-extended differentials on the opposite polynomial site. -/
def omegaSheaf : (Algebra.PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B :=
  unopUnop (Algebra.PolynomialOver A B) ⋙ omegaSheafCov A B

/-- Evaluation on a double-opposite object gives its scalar-extended differential module. -/
theorem omegaSheaf_obj (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (omegaSheaf A B).obj X = omegaSheafObj (unop (unop X)) := rfl

/-- Evaluation on a double-opposite morphism gives its induced differential map. -/
theorem omegaSheaf_map {X Y : (Algebra.PolynomialSite A B)ᵒᵖ} (f : X ⟶ Y) :
    (omegaSheaf A B).map f = omegaSheafMap f.unop.unop := rfl

end CommAlgCat.Over.Polynomial.Site
