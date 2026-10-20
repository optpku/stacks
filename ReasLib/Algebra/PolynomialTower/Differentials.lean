/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite.Differentials
public import ReasLib.Algebra.PolynomialTower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Differential transitivity on polynomial squares

The three projections of polynomial squares carry a canonical sequence of
scalar-extended differential modules, and hence a sequence of sheaves for the bottom topology.
-/

@[expose] public section

open CategoryTheory Opposite
open CommAlgCat.Over.Polynomial.Site
open scoped TensorProduct ChangeOfRings

noncomputable section

universe u

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

namespace Algebra.PolynomialTower

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Differentials of the first polynomial algebra, extended to the intermediate base. -/
def inverseImageOmega1 : PolynomialTower A B C ⥤ ModuleCat.{u} B :=
  forgetToBase A B C ⋙ omegaSheafCov A B

/-- Differentials of the second polynomial algebra over the initial base, extended to the target. -/
def inverseImageOmega2 : PolynomialTower A B C ⥤ ModuleCat.{u} C :=
  forgetToOverA A B C ⋙ omegaSheafCov A C

/-- Relative differentials after tensor base change to the intermediate base. -/
def inverseImageOmega3 : PolynomialTower A B C ⥤ ModuleCat.{u} C :=
  forgetToOverB A B C ⋙ omegaSheafCov B C

/-- The first differential functor evaluates on the first augmented polynomial algebra. -/
theorem inverseImageOmega1_obj (X : PolynomialTower A B C) :
    (inverseImageOmega1 A B C).obj X = omegaSheafObj (base X) := rfl

/-- The second differential functor evaluates on the second augmented polynomial algebra. -/
theorem inverseImageOmega2_obj (X : PolynomialTower A B C) :
    (inverseImageOmega2 A B C).obj X = omegaSheafObj (overA X) := rfl

/-- The relative differential functor evaluates on the tensor base change. -/
theorem inverseImageOmega3_obj (X : PolynomialTower A B C) :
    (inverseImageOmega3 A B C).obj X = omegaSheafObj (tensorOverBase X) := rfl

/-- The first differential module extended further to the final target ring. -/
def tensorOmega1Obj (X : PolynomialTower A B C) : ModuleCat.{u} C :=
  (ModuleCat.extendScalars (algebraMap B C)).obj ((inverseImageOmega1 A B C).obj X)

/-- Extension of scalars of the first differential functor to the final target ring. -/
def tensorOmega1 : PolynomialTower A B C ⥤ ModuleCat.{u} C :=
  inverseImageOmega1 A B C ⋙ ModuleCat.extendScalars (algebraMap B C)

/-- Evaluation commutes with extension of scalars of the first differential functor. -/
theorem tensorOmega1_obj (X : PolynomialTower A B C) :
    (tensorOmega1 A B C).obj X = tensorOmega1Obj A B C X := rfl

/-- The first term is the scalar extension of the first inverse-image differential functor. -/
theorem tensorOmega1_eq_extendScalars :
    tensorOmega1 A B C =
      inverseImageOmega1 A B C ⋙ ModuleCat.extendScalars (algebraMap B C) := rfl

variable {A B C}

private instance algebraPQ (X : PolynomialTower A B C) : Algebra (P X) (Q X) :=
  (toQ X).hom.toRingHom.toAlgebra

private instance algebraPB (X : PolynomialTower A B C) : Algebra (P X) B :=
  algebraToBase (base X)

private instance algebraQC (X : PolynomialTower A B C) : Algebra (Q X) C :=
  algebraToBase (overA X)

private instance algebraPC (X : PolynomialTower A B C) : Algebra (P X) C :=
  ((toC X).hom.toRingHom.comp (toQ X).hom.toRingHom).toAlgebra

private instance towerAPQ (X : PolynomialTower A B C) : IsScalarTower A (P X) (Q X) :=
  IsScalarTower.of_algHom (toQ X).hom

private instance towerPQC (X : PolynomialTower A B C) : IsScalarTower (P X) (Q X) C :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

private instance towerPBC (X : PolynomialTower A B C) : IsScalarTower (P X) B C :=
  IsScalarTower.of_algebraMap_eq fun p ↦ (toCOverP_commutes X p).symm

private instance towerAQC (X : PolynomialTower A B C) : IsScalarTower A (Q X) C :=
  IsScalarTower.of_algHom (toC X).hom

private instance algebraQTensor (X : PolynomialTower A B C) :
    Algebra (Q X) (tensorOverBase X).obj.left :=
  by
    change Algebra (Q X) ((Q X) ⊗[P X] B)
    exact Algebra.TensorProduct.leftAlgebra

private instance algebraPTensor (X : PolynomialTower A B C) :
    Algebra (P X) (tensorOverBase X).obj.left :=
  by
    change Algebra (P X) ((Q X) ⊗[P X] B)
    exact Algebra.TensorProduct.instAlgebra

private instance towerPQTensor (X : PolynomialTower A B C) :
    IsScalarTower (P X) (Q X) (tensorOverBase X).obj.left := by
  change IsScalarTower (P X) (Q X) ((Q X) ⊗[P X] B)
  infer_instance

private instance towerPBTensor (X : PolynomialTower A B C) :
    IsScalarTower (P X) B (tensorOverBase X).obj.left := by
  change @IsScalarTower (P X) B ((Q X) ⊗[P X] B) _
    (Algebra.TensorProduct.rightAlgebra (R := P X) (A := Q X) (B := B)).toSMul _
  exact Algebra.TensorProduct.right_isScalarTower

private instance pushoutTensor (X : PolynomialTower A B C) :
    Algebra.IsPushout (P X) B (Q X) (tensorOverBase X).obj.left := by
  exact @TensorProduct.isPushout' (P X) (Q X) B _ _ _ (algebraPQ X) (algebraPB X)

private instance algebraTensorC (X : PolynomialTower A B C) :
    Algebra (tensorOverBase X).obj.left C :=
  algebraToBase (tensorOverBase X)

private instance towerQTensorC (X : PolynomialTower A B C) :
    IsScalarTower (Q X) (tensorOverBase X).obj.left C :=
  IsScalarTower.of_algebraMap_eq fun q ↦ by
    change toC X q = toC X q * algebraMap B C 1
    simp

private def extendScalarsObjIso (M : ModuleCat.{u} B) :
    (ModuleCat.extendScalars (algebraMap B C)).obj M ≅ ModuleCat.of C (C ⊗[B] M) :=
  eqToIso (by
    have h : Module.compHom C (algebraMap B C) = (inferInstance : Module B C) :=
      Module.ext' _ _ fun b c ↦ (Algebra.smul_def b c).symm
    let F (m : Module B C) (hc : @SMulCommClass B C C m.toSMul _) : ModuleCat.{u} C :=
      @ModuleCat.of C _ (@TensorProduct B _ C M _ _ m _) _
        (@TensorProduct.leftModule B C _ _ C M _ _ _ m _ hc)
    change F (Module.compHom C (algebraMap B C))
      (@SMulCommClass.mk B C C (Module.compHom C (algebraMap B C)).toSMul _
        (fun b c x ↦ by
          change algebraMap B C b * (c * x) = c * (algebraMap B C b * x)
          rw [← mul_assoc, mul_comm (algebraMap B C b) c, mul_assoc])) = F _ _
    congr 1)

variable (A B C)

/-- The first transitivity map is differential functoriality followed by scalar-extension cancellation. -/
def toOmega2App (X : PolynomialTower A B C) :
    (tensorOmega1 A B C).obj X ⟶ (inverseImageOmega2 A B C).obj X :=
  (extendScalarsObjIso ((inverseImageOmega1 A B C).obj X)).hom ≫
    ModuleCat.ofHom
      (KaehlerDifferential.tensorMapBaseChange A (P X) (Q X) C ∘ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          (P X) B C C (KaehlerDifferential A (P X))).toLinearMap)

/-- The first map sends a double tensor of a differential to the differential of its image. -/
theorem toOmega2App_tmul_D (X : PolynomialTower A B C) (c : C) (b : B) (p : P X) :
    (toOmega2App A B C X).hom
      (c ⊗ₜ[B, algebraMap B C]
        (show (inverseImageOmega1 A B C).obj X from
          (show B ⊗[P X] KaehlerDifferential A (P X) from
            b ⊗ₜ[P X] KaehlerDifferential.D A (P X) p))) =
      (c * algebraMap B C b) ⊗ₜ[Q X] KaehlerDifferential.D A (Q X) (toQ X p) := by
  sorry

/-- The first transitivity map commutes with morphisms of polynomial squares. -/
theorem toOmega2_naturality {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    (tensorOmega1 A B C).map f ≫ toOmega2App A B C Y =
      toOmega2App A B C X ≫ (inverseImageOmega2 A B C).map f := by
  sorry

/-- The natural first transitivity map on polynomial squares. -/
def toOmega2 : tensorOmega1 A B C ⟶ inverseImageOmega2 A B C where
  app := toOmega2App A B C
  naturality _ _ f := toOmega2_naturality A B C f

/-- Differential base change identifies the relative differential module with the third term. -/
def omega3Iso (X : PolynomialTower A B C) :
    ModuleCat.of C (C ⊗[Q X] KaehlerDifferential (P X) (Q X)) ≅
      (inverseImageOmega3 A B C).obj X :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange
    (Q X) (tensorOverBase X).obj.left C C (KaehlerDifferential (P X) (Q X))).symm.toModuleIso ≪≫
    ((KaehlerDifferential.tensorKaehlerEquiv (P X) B (Q X) (tensorOverBase X).obj.left).baseChange
      (tensorOverBase X).obj.left C _ _).toModuleIso

/-- Differential base change sends a differential to the differential of the left tensor inclusion. -/
theorem omega3Iso_tmul_D (X : PolynomialTower A B C) (c : C) (q : Q X) :
    (omega3Iso A B C X).hom (c ⊗ₜ[Q X] KaehlerDifferential.D (P X) (Q X) q) =
      c ⊗ₜ[(tensorOverBase X).obj.left]
        KaehlerDifferential.D B (tensorOverBase X).obj.left
          (Algebra.TensorProduct.includeLeftRingHom q) := by
  sorry

/-- The second transitivity map is the relative differential map followed by differential base change. -/
def toOmega3App (X : PolynomialTower A B C) :
    (inverseImageOmega2 A B C).obj X ⟶ (inverseImageOmega3 A B C).obj X :=
  by
  change ModuleCat.of C (C ⊗[Q X] KaehlerDifferential A (Q X)) ⟶ _
  exact ModuleCat.ofHom ((KaehlerDifferential.map A (P X) (Q X) (Q X)).baseChange C) ≫
    (omega3Iso A B C X).hom

/-- The second map sends a differential to its relative differential in the tensor base change. -/
theorem toOmega3App_tmul_D (X : PolynomialTower A B C) (c : C) (q : Q X) :
    (toOmega3App A B C X).hom (show C ⊗[Q X] KaehlerDifferential A (Q X) from
      c ⊗ₜ[Q X] KaehlerDifferential.D A (Q X) q) =
      c ⊗ₜ[(tensorOverBase X).obj.left]
        KaehlerDifferential.D B (tensorOverBase X).obj.left
          (Algebra.TensorProduct.includeLeftRingHom q) := by
  sorry

/-- The second transitivity map commutes with morphisms of polynomial squares. -/
theorem toOmega3_naturality {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    (inverseImageOmega2 A B C).map f ≫ toOmega3App A B C Y =
      toOmega3App A B C X ≫ (inverseImageOmega3 A B C).map f := by
  sorry

/-- The natural second transitivity map on polynomial squares. -/
def toOmega3 : inverseImageOmega2 A B C ⟶ inverseImageOmega3 A B C where
  app := toOmega3App A B C
  naturality _ _ f := toOmega3_naturality A B C f

/-- The composite of the two differential transitivity maps vanishes. -/
theorem omegaSequence_zero : toOmega2 A B C ≫ toOmega3 A B C = 0 := by
  sorry

/-- The differential transitivity complex of functors on polynomial squares. -/
def omegaSequence : ShortComplex (PolynomialTower A B C ⥤ ModuleCat.{u} C) :=
  ShortComplex.mk (toOmega2 A B C) (toOmega3 A B C) (omegaSequence_zero A B C)

/-- Evaluation of the differential transitivity complex at a polynomial square. -/
def omegaSequence_app (X : PolynomialTower A B C) : ShortComplex (ModuleCat.{u} C) :=
  (omegaSequence A B C).map ((evaluation _ _).obj X)

/-- The differential transitivity complex is short exact at every polynomial square. -/
theorem omegaSequence_app_shortExact (X : PolynomialTower A B C) :
    (omegaSequence_app A B C X).ShortExact := by
  sorry

/-- The differential transitivity complex is short exact in the functor category. -/
theorem omegaSequence_shortExact : (omegaSequence A B C).ShortExact := by
  sorry

/-- The differential transitivity complex as module-valued sheaves on the opposite polynomial-square site. -/
def omegaSheafSequence : ShortComplex
    (Sheaf (⊥ : GrothendieckTopology (PolynomialTower A B C)ᵒᵖ) (ModuleCat.{u} C)) :=
  ((omegaSequence A B C).map
    ((Functor.whiskeringLeft _ _ _).obj (unopUnop (PolynomialTower A B C)))).map
      (sheafBotEquivalence (C := (PolynomialTower A B C)ᵒᵖ) (ModuleCat.{u} C)).inverse

/-- The canonical differential transitivity sequence of sheaves is short exact. -/
theorem omegaSheafSequence_shortExact : (omegaSheafSequence A B C).ShortExact := by
  sorry

end Algebra.PolynomialTower
