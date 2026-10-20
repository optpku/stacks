module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Model
public import ReasLib.Algebra.Homology.Embedding.Functor
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Derived
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.CompletionPresentation

/-!
# Comparison of completed naive cotangent complexes with tensor base change

The component comparisons identify the completed Jacobian complex of the completed presentation
of `B^∧` with the two-term tensor model of `NL(α)`, and compare the resulting
object of `D(B^∧)` with derived extension of scalars of `NL_{B/A}`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open Algebra.Extension
open Algebra.Extension.NaiveCotangent
open Algebra.NaiveCotangent.Adic
open scoped TensorProduct

namespace Algebra.NaiveCotangent.Adic

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {B : Type u} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
variable {ι : Type u} [Fintype ι]

variable (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) in
/-- The inclusion of `J = ker(α)` into `A[x_ι]`. -/
private def polynomialKerSubtype :
    (polynomialExtension α hα).ker →ₗ[(polynomialExtension α hα).Ring] (polynomialExtension α hα).Ring :=
  (polynomialExtension α hα).ker.subtype

variable (I : Ideal A)
variable (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α)

/-- The canonical finite-free identification of the cotangent space of `α`
with the free module on the variables. -/
private def cotangentSpaceFunEquiv :
    (polynomialExtension α hα).CotangentSpace ≃ₗ[B] (ι → B) :=
  (Algebra.Generators.ofAlgHom α hα).cotangentSpaceBasis.equivFun

/-- Degree-zero identification `B^∧ ⊗_B Ω(α) ≃ (ι → B^∧)`. -/
@[no_expose] def freeCotangentSpaceEquiv :
    algebraCompletion I B ⊗[B] (polynomialExtension α hα).CotangentSpace ≃ₗ[algebraCompletion I B]
      (ι → algebraCompletion I B) :=
  open Classical in
    (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (algebraCompletion I B) (algebraCompletion I B))
        (cotangentSpaceFunEquiv α hα)).trans
      (TensorProduct.piScalarRight B (algebraCompletion I B) (algebraCompletion I B) ι)

/-- The canonical `B^∧`-linear map `B^∧ ⊗_B (J / J²) → J^∧ / (J^∧)²` induced by
the morphism of presentations from `α` to the completed presentation of `B^∧`. -/
def cotangentTensorHom :
    algebraCompletion I B ⊗[B] (polynomialExtension α hα).Cotangent →ₗ[algebraCompletion I B]
      (completionPresentation I α hα).toExtension.Cotangent :=
  (Cotangent.map (polynomialToCompletionHom I α hα)).liftBaseChange (algebraCompletion I B)

/-- Completion-as-tensor for the conormal module of `α`:
`B^∧ ⊗_B (J / J²) ≃ (J / J²)^∧`. -/
def cotangentTensorCompletionEquiv :
    algebraCompletion I B ⊗[B] (polynomialExtension α hα).Cotangent ≃ₗ[algebraCompletion I B]
      AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent :=
  @AdicCompletion.ofTensorProductEquivOfFiniteNoetherian B _ (I.map (algebraMap A B))
    (polynomialExtension α hα).Cotangent _ _
    (Algebra.FiniteType.isNoetherianRing A B)
    (Cotangent.finite
      ((isNoetherianRing_iff_ideal_fg (R := MvPolynomial ι A)).mp inferInstance
        (polynomialExtension α hα).ker))

/-- The map `(J / J²)^∧ → J^∧ / (J^∧)²` induced by `Cotangent.map` of the
presentation morphism from `α` to the completed presentation. -/
def cotangentCompletionHom :
    AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent
      →ₗ[algebraCompletion I B]
      (completionPresentation I α hα).toExtension.Cotangent :=
  cotangentTensorHom I α hα ∘ₗ
    (cotangentTensorCompletionEquiv I α hα).symm.toLinearMap

/-- Completing the inclusion `J ↪ A[x_ι]` lands in the kernel of
`completionAlgHom`. -/
private theorem kerCompletion_range_eq :
    LinearMap.range
        (AdicCompletion.map (I.map (algebraMap A (polynomialExtension α hα).Ring))
          (polynomialKerSubtype α hα)) =
      (completionPresentation I α hα).ker :=
  sorry

/-- Identification of `ker(completionAlgHom)` with the `I A[x_ι]`-adic
completion of `J = ker(α)`. -/
@[no_expose] def kerCompletionEquiv :=
  (LinearEquiv.ofInjective
      (AdicCompletion.map (I.map (algebraMap A (polynomialExtension α hα).Ring))
        (polynomialKerSubtype α hα))
      (@AdicCompletion.map_injective (polynomialExtension α hα).Ring _
        (I.map (algebraMap A (polynomialExtension α hα).Ring))
        (polynomialExtension α hα).ker _ _ (polynomialExtension α hα).Ring _ _
        (inferInstanceAs (IsNoetherianRing (MvPolynomial ι A)))
        (inferInstanceAs (Module.Finite (polynomialExtension α hα).Ring
          (polynomialExtension α hα).Ring))
        (polynomialKerSubtype α hα)
        (polynomialExtension α hα).ker.injective_subtype)).trans
    (LinearEquiv.ofEq _ _ (kerCompletion_range_eq I α hα))

/-- The identification of kernels extends the completed inclusion of `J`. -/
theorem kerCompletionEquiv_subtype
    (x : AdicCompletion (I.map (algebraMap A (polynomialExtension α hα).Ring)) (polynomialExtension α hα).ker) :
    (kerCompletionEquiv I α hα x).val =
      AdicCompletion.map (I.map (algebraMap A (polynomialExtension α hα).Ring))
        ((polynomialExtension α hα).ker.subtype :
          (polynomialExtension α hα).ker →ₗ[(polynomialExtension α hα).Ring] (polynomialExtension α hα).Ring) x :=
  sorry

/-- Each finite adic stage of `J / J²` as an `A[x_ι]`-module is contained in
the corresponding stage as a `B`-module. -/
private theorem cotangentStageSubmodule_le (n : ℕ) :
    ((I.map (algebraMap A (polynomialExtension α hα).Ring) ^ n • ⊤ :
          Submodule (polynomialExtension α hα).Ring
            (polynomialExtension α hα).Cotangent).restrictScalars A) ≤
      (((I.map (algebraMap A B)) ^ n • ⊤ :
          Submodule B (polynomialExtension α hα).Cotangent).restrictScalars A) :=
  sorry

/-- The comparison of finite adic stages of `J / J²` along `A[x_ι]` and along `B`. -/
private def cotangentStageFactor (n : ℕ) :
    (polynomialExtension α hα).Cotangent ⧸
        (I.map (algebraMap A (polynomialExtension α hα).Ring) ^ n • ⊤ :
          Submodule (polynomialExtension α hα).Ring (polynomialExtension α hα).Cotangent) →ₗ[A]
      (polynomialExtension α hα).Cotangent ⧸
        ((I.map (algebraMap A B)) ^ n • ⊤ :
          Submodule B (polynomialExtension α hα).Cotangent) :=
  (Submodule.Quotient.restrictScalarsEquiv A
      ((I.map (algebraMap A B)) ^ n • ⊤ :
        Submodule B (polynomialExtension α hα).Cotangent)).toLinearMap ∘ₗ
    Submodule.factor (cotangentStageSubmodule_le I α hα n) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv A
          (I.map (algebraMap A (polynomialExtension α hα).Ring) ^ n • ⊤ :
            Submodule (polynomialExtension α hα).Ring
              (polynomialExtension α hα).Cotangent)).symm.toLinearMap

/-- The finite-stage conormal comparison commutes with adic transition maps. -/
private theorem cotangentAdicChangeOfRing_compatible
    (x : AdicCompletion (I.map (algebraMap A (polynomialExtension α hα).Ring)) (polynomialExtension α hα).Cotangent)
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap (I.map (algebraMap A B))
        (polynomialExtension α hα).Cotangent hmn
        (cotangentStageFactor I α hα n
          (AdicCompletion.eval (I.map (algebraMap A (polynomialExtension α hα).Ring))
            (polynomialExtension α hα).Cotangent n x)) =
      cotangentStageFactor I α hα m
        (AdicCompletion.eval (I.map (algebraMap A (polynomialExtension α hα).Ring))
          (polynomialExtension α hα).Cotangent m x) :=
  sorry

/-- The compatible finite-stage conormal comparisons define a completed element. -/
private def cotangentAdicChangeOfRingValue
    (x : AdicCompletion (I.map (algebraMap A (polynomialExtension α hα).Ring)) (polynomialExtension α hα).Cotangent) :
    AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent :=
  ⟨fun n ↦ cotangentStageFactor I α hα n
      (AdicCompletion.eval (I.map (algebraMap A (polynomialExtension α hα).Ring))
        (polynomialExtension α hα).Cotangent n x),
    fun hmn ↦ cotangentAdicChangeOfRing_compatible I α hα x hmn⟩

/-- The completed change of coefficient ring preserves addition. -/
private theorem cotangentAdicChangeOfRingValue_add
    (x y : AdicCompletion (I.map (algebraMap A (polynomialExtension α hα).Ring)) (polynomialExtension α hα).Cotangent) :
    cotangentAdicChangeOfRingValue I α hα (x + y) =
      cotangentAdicChangeOfRingValue I α hα x + cotangentAdicChangeOfRingValue I α hα y :=
  sorry

/-- The completed change of coefficient ring commutes with base-ring scalars. -/
private theorem cotangentAdicChangeOfRingValue_smul (a : A)
    (x : AdicCompletion (I.map (algebraMap A (polynomialExtension α hα).Ring)) (polynomialExtension α hα).Cotangent) :
    cotangentAdicChangeOfRingValue I α hα (a • x) =
      a • cotangentAdicChangeOfRingValue I α hα x :=
  sorry

/-- Completing the conormal module along the extended polynomial ideal maps to
its completion along the extended ideal of the target algebra. -/
private def cotangentAdicChangeOfRing :
    AdicCompletion (I.map (algebraMap A (polynomialExtension α hα).Ring)) (polynomialExtension α hα).Cotangent
      →ₗ[A]
      AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent where
  toFun := cotangentAdicChangeOfRingValue I α hα
  map_add' := cotangentAdicChangeOfRingValue_add I α hα
  map_smul' := cotangentAdicChangeOfRingValue_smul I α hα

/-- Evaluating the change-of-rings comparison of completed conormals at a finite
adic stage recovers `cotangentStageFactor`. -/
private theorem cotangentAdicChangeOfRing_eval (n : ℕ)
    (x : AdicCompletion (I.map (algebraMap A (polynomialExtension α hα).Ring)) (polynomialExtension α hα).Cotangent) :
    (cotangentAdicChangeOfRing I α hα x).val n =
      cotangentStageFactor I α hα n
        (AdicCompletion.eval (I.map (algebraMap A (polynomialExtension α hα).Ring))
          (polynomialExtension α hα).Cotangent n x) :=
  sorry

/-- A completed kernel element maps to the completion of its conormal class. -/
private def presentationKerToCotangentCompletionValue
    (y : ((completionPresentation I α hα).ker).restrictScalars A) :
    AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent :=
  cotangentAdicChangeOfRing I α hα
    (AdicCompletion.map (I.map (algebraMap A (polynomialExtension α hα).Ring))
      (Cotangent.mk :
          (polynomialExtension α hα).ker →ₗ[(polynomialExtension α hα).Ring]
            (polynomialExtension α hα).Cotangent)
      ((kerCompletionEquiv I α hα).symm
        ⟨(y : polynomialCompletion A I ι), y.2⟩))

/-- Passage from completed kernel elements to completed conormal classes preserves addition. -/
private theorem presentationKerToCotangentCompletionValue_add
    (x y : ((completionPresentation I α hα).ker).restrictScalars A) :
    presentationKerToCotangentCompletionValue I α hα (x + y) =
      presentationKerToCotangentCompletionValue I α hα x +
        presentationKerToCotangentCompletionValue I α hα y :=
  sorry

/-- Passage from completed kernel elements to completed conormal classes
commutes with base-ring scalars. -/
private theorem presentationKerToCotangentCompletionValue_smul (a : A)
    (x : ((completionPresentation I α hα).ker).restrictScalars A) :
    presentationKerToCotangentCompletionValue I α hα (a • x) =
      a • presentationKerToCotangentCompletionValue I α hα x :=
  sorry

/-- Completing the quotient from the original kernel to its conormal module
maps the completed presentation kernel to the completed conormal module. -/
private def presentationKerToCotangentCompletion :
    ((completionPresentation I α hα).ker).restrictScalars A →ₗ[A]
      AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent where
  toFun := presentationKerToCotangentCompletionValue I α hα
  map_add' := presentationKerToCotangentCompletionValue_add I α hα
  map_smul' := presentationKerToCotangentCompletionValue_smul I α hα

/-- The completed kernel-to-conormal map annihilates the square of the completed kernel. -/
private theorem cotangentCompletionHomInv_killsSquare :
    (((completionPresentation I α hα).ker • ⊤ :
        Submodule (polynomialCompletion A I ι)
          (completionPresentation I α hα).ker).restrictScalars A) ≤
      LinearMap.ker (presentationKerToCotangentCompletion I α hα) :=
  sorry

/-- A completed conormal class maps to the completed original conormal module
by descending the completed kernel-to-conormal map. -/
private def cotangentCompletionHomInvValue
    (x : (completionPresentation I α hα).toExtension.Cotangent) :
    AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent :=
  Submodule.liftQ
    (((completionPresentation I α hα).ker • ⊤ :
          Submodule (polynomialCompletion A I ι)
            (completionPresentation I α hα).ker).restrictScalars A)
    (presentationKerToCotangentCompletion I α hα)
    (cotangentCompletionHomInv_killsSquare I α hα)
    ((Submodule.Quotient.restrictScalarsEquiv A
        ((completionPresentation I α hα).ker • ⊤ :
          Submodule (polynomialCompletion A I ι)
            (completionPresentation I α hα).ker)).symm
      (Algebra.Extension.Cotangent.val x))

/-- The descended completed conormal map preserves addition. -/
private theorem cotangentCompletionHomInvValue_add
    (x y : (completionPresentation I α hα).toExtension.Cotangent) :
    cotangentCompletionHomInvValue I α hα (x + y) =
      cotangentCompletionHomInvValue I α hα x + cotangentCompletionHomInvValue I α hα y :=
  sorry

/-- The descended completed conormal map commutes with completed-algebra scalars. -/
private theorem cotangentCompletionHomInvValue_smul (b : algebraCompletion I B)
    (x : (completionPresentation I α hα).toExtension.Cotangent) :
    cotangentCompletionHomInvValue I α hα (b • x) =
      b • cotangentCompletionHomInvValue I α hα x :=
  sorry

/-- The inverse completed conormal map is obtained by completing the original
kernel-to-conormal quotient and descending through the completed kernel square. -/
@[no_expose] def cotangentCompletionHomInv :
    (completionPresentation I α hα).toExtension.Cotangent
      →ₗ[algebraCompletion I B]
      AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent where
  toFun := cotangentCompletionHomInvValue I α hα
  map_add' := cotangentCompletionHomInvValue_add I α hα
  map_smul' := cotangentCompletionHomInvValue_smul I α hα

/-- The inverse completed conormal map is a left inverse of the forward map. -/
private theorem cotangentCompletionHom_left_inv :
    cotangentCompletionHomInv I α hα ∘ₗ cotangentCompletionHom I α hα = LinearMap.id :=
  sorry

/-- The inverse completed conormal map is a right inverse of the forward map. -/
private theorem cotangentCompletionHom_right_inv :
    cotangentCompletionHom I α hα ∘ₗ cotangentCompletionHomInv I α hα = LinearMap.id :=
  sorry

/-- The completion of the original conormal module is linearly equivalent to
the conormal module of the completed presentation. -/
@[no_expose] def cotangentCompletionEquiv :
    AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent
      ≃ₗ[algebraCompletion I B]
      (completionPresentation I α hα).toExtension.Cotangent :=
  LinearEquiv.ofLinear (cotangentCompletionHom I α hα)
    (cotangentCompletionHomInv I α hα)
    (cotangentCompletionHom_right_inv I α hα) (cotangentCompletionHom_left_inv I α hα)

/-- Degree-one identification `(J / J²) ⊗_B B^∧ ≃ J^∧ / (J^∧)²`, as the
completion-as-tensor equivalence followed by `(J / J²)^∧ ≃ J^∧ / (J^∧)²`. -/
def cotangentTensorEquiv :
    algebraCompletion I B ⊗[B] (polynomialExtension α hα).Cotangent ≃ₗ[algebraCompletion I B]
      (completionPresentation I α hα).toExtension.Cotangent :=
  (cotangentTensorCompletionEquiv I α hα).trans (cotangentCompletionEquiv I α hα)

/-- Evaluating the degree-one identification on elementary tensors recovers the
induced conormal map. -/
theorem cotangentTensorEquiv_tmul (x : algebraCompletion I B)
    (m : (polynomialExtension α hα).Cotangent) :
    cotangentTensorEquiv I α hα (x ⊗ₜ m) =
      x • Cotangent.map (polynomialToCompletionHom I α hα) m :=
  sorry

/-- The degree-one inverse recovers
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian.symm` on the image of
`Cotangent.map`. -/
theorem cotangentTensorEquiv_symm_of (m : (polynomialExtension α hα).Cotangent) :
    (cotangentTensorEquiv I α hα).symm
        (Cotangent.map (polynomialToCompletionHom I α hα) m) =
      (cotangentTensorCompletionEquiv I α hα).symm
        (AdicCompletion.of (I.map (algebraMap A B))
          (polynomialExtension α hα).Cotangent m) :=
  sorry

/-- The degree-one inverse composed with the completed conormal map is
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian.symm`. -/
theorem cotangentTensorEquiv_symm_completionHom :
    (cotangentTensorEquiv I α hα).symm.toLinearMap ∘ₗ cotangentCompletionHom I α hα =
      (cotangentTensorCompletionEquiv I α hα).symm.toLinearMap :=
  sorry

/-- Specification of the degree-one identification as the unique `B^∧`-linear
extension of the conormal map of `polynomialToCompletionHom`. -/
theorem cotangentTensorEquiv_spec :
    (cotangentTensorEquiv I α hα).toLinearMap = cotangentTensorHom I α hα :=
  sorry

/-- Degree-zero component of the complex identification
`NL_{B^∧/A}^∧ ≅ NL(α) ⊗_B B^∧`. -/
private def tensorIsoComponentZero :
    (naiveCotangent I (completionPresentation I α hα)).X 0 ≅
      (BaseChange.tensorModel (polynomialExtension α hα)).X 0 :=
  (componentZeroIso (completionPresentation I α hα)).trans
    (freeCotangentSpaceEquiv I α hα).symm.toModuleIso

/-- Degree-one component of the complex identification
`NL_{B^∧/A}^∧ ≅ NL(α) ⊗_B B^∧`. -/
private def tensorIsoComponentOne :
    (naiveCotangent I (completionPresentation I α hα)).X 1 ≅
      (BaseChange.tensorModel (polynomialExtension α hα)).X 1 :=
  (componentOneIso (completionPresentation I α hα)).trans
    (cotangentTensorEquiv I α hα).symm.toModuleIso

/-- Higher components of the completed Jacobian complex are the zero object
of `ModuleCat`. -/
private def naiveCotangentComponentSuccIsoUnit (n : ℕ) :
    (naiveCotangent I (completionPresentation I α hα)).X (n + 2) ≅
      ModuleCat.of (algebraCompletion I B) PUnit :=
  ChainComplex.mk'XIso
    (ModuleCat.of (algebraCompletion I B) (ι → algebraCompletion I B))
    (ModuleCat.of (algebraCompletion I B)
      (completionPresentation I α hα).toExtension.Cotangent)
    (ModuleCat.ofHom (jacobian (completionPresentation I α hα)))
    (fun {_ _} _ ↦
      ⟨ModuleCat.of (algebraCompletion I B) PUnit, 0, zero_comp⟩)
    n

/-- Higher components of the tensor model of `NL(α)` are the zero object of
`ModuleCat`. -/
private def tensorModelComponentSuccIsoUnit (n : ℕ) :
    (BaseChange.tensorModel (polynomialExtension α hα) :
        ChainComplex (ModuleCat (algebraCompletion I B)) ℕ).X (n + 2) ≅
      ModuleCat.of (algebraCompletion I B) PUnit :=
  ChainComplex.mk'XIso
    (ModuleCat.of (algebraCompletion I B)
      (algebraCompletion I B ⊗[B] (polynomialExtension α hα).CotangentSpace))
    (ModuleCat.of (algebraCompletion I B)
      (algebraCompletion I B ⊗[B] (polynomialExtension α hα).Cotangent))
    (ModuleCat.ofHom
      (LinearMap.baseChange (algebraCompletion I B)
        (polynomialExtension α hα).cotangentComplex))
    (fun {_ _} _ ↦
      ⟨ModuleCat.of (algebraCompletion I B) PUnit, 0, zero_comp⟩)
    n

/-- Higher components of both two-term complexes are identified through the
definitional zero object `ModuleCat.of _ PUnit`. -/
private def tensorIsoComponentSucc (n : ℕ) :
    (naiveCotangent I (completionPresentation I α hα)).X (n + 2) ≅
      (BaseChange.tensorModel (polynomialExtension α hα) :
          ChainComplex (ModuleCat (algebraCompletion I B)) ℕ).X (n + 2) :=
  (naiveCotangentComponentSuccIsoUnit I α hα n).trans
    (tensorModelComponentSuccIsoUnit I α hα n).symm

/-- Components of the complex identification in every homological degree. -/
private def tensorIsoComponent :
    ∀ n : ℕ,
      (naiveCotangent I (completionPresentation I α hα)).X n ≅
        (BaseChange.tensorModel (polynomialExtension α hα)).X n
  | 0 => tensorIsoComponentZero I α hα
  | 1 => tensorIsoComponentOne I α hα
  | n + 2 => tensorIsoComponentSucc I α hα n

/-- The componentwise identification commutes with differentials. -/
private theorem tensorIsoComponent_comm (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (tensorIsoComponent I α hα i).hom ≫
        (BaseChange.tensorModel (polynomialExtension α hα)).d i j =
      (naiveCotangent I (completionPresentation I α hα)).d i j ≫
        (tensorIsoComponent I α hα j).hom :=
  sorry

/-- The completed Jacobian complex of a completed polynomial presentation is
isomorphic to the tensor base change of its ordinary naive cotangent complex. -/
@[no_expose] def tensorIso :
    naiveCotangent I (completionPresentation I α hα) ≅
      BaseChange.tensorModel (polynomialExtension α hα) :=
  HomologicalComplex.Hom.isoOfComponents (tensorIsoComponent I α hα)
    (tensorIsoComponent_comm I α hα)

/-- In degree zero, the complex comparison is the inverse finite-free tensor equivalence. -/
theorem tensorIso_X_zero :
    (tensorIso I α hα).hom.f 0 =
      ((componentZeroIso (completionPresentation I α hα)).trans
        (freeCotangentSpaceEquiv I α hα).symm.toModuleIso).hom :=
  sorry

/-- In degree one, the complex comparison is the inverse conormal tensor equivalence. -/
theorem tensorIso_X_one :
    (tensorIso I α hα).hom.f 1 =
      ((componentOneIso (completionPresentation I α hα)).trans
        (cotangentTensorEquiv I α hα).symm.toModuleIso).hom :=
  sorry

/-- The identification intertwines the completed Jacobian with the base-changed
cotangent differential of `α`. -/
theorem tensorIso_d_one_zero :
    (tensorIso I α hα).hom.f 1 ≫
        (BaseChange.tensorModel (polynomialExtension α hα)).d 1 0 =
      (naiveCotangent I (completionPresentation I α hα)).d 1 0 ≫
        (tensorIso I α hα).hom.f 0 :=
  sorry

/-- Passage from the completed Jacobian complex to the literal scalar extension
of `NL(α)`. -/
def tensorIso_comp_scalarExtension :
    naiveCotangent I (completionPresentation I α hα) ≅
      BaseChange.scalarExtension (polynomialExtension α hα) :=
  (tensorIso I α hα).trans
    (BaseChange.scalarExtensionIsoTensorModel (polynomialExtension α hα)).symm

/-- The localized forward and inverse homotopy maps compose to the identity. -/
private theorem derivedIsoOfHomotopyEquiv_hom_inv_id
    {T : Type u} [CommRing T] {K L : CochainComplex (ModuleCat T) ℤ}
    (h : HomotopyEquiv K L) :
    DerivedCategory.Q.map h.hom ≫ DerivedCategory.Q.map h.inv =
      𝟙 (DerivedCategory.Q.obj K) :=
  sorry

/-- The localized inverse and forward homotopy maps compose to the identity. -/
private theorem derivedIsoOfHomotopyEquiv_inv_hom_id
    {T : Type u} [CommRing T] {K L : CochainComplex (ModuleCat T) ℤ}
    (h : HomotopyEquiv K L) :
    DerivedCategory.Q.map h.inv ≫ DerivedCategory.Q.map h.hom =
      𝟙 (DerivedCategory.Q.obj L) :=
  sorry

/-- A homotopy equivalence induces an isomorphism after derived localization. -/
private def derivedIsoOfHomotopyEquiv
    {T : Type u} [CommRing T] {K L : CochainComplex (ModuleCat T) ℤ}
    (h : HomotopyEquiv K L) :
    DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L where
  hom := DerivedCategory.Q.map h.hom
  inv := DerivedCategory.Q.map h.inv
  hom_inv_id := derivedIsoOfHomotopyEquiv_hom_inv_id h
  inv_hom_id := derivedIsoOfHomotopyEquiv_inv_hom_id h

/-- Presentation-independence homotopy equivalence from `NL(α)` to the canonical
`NL_{B/A}`. -/
private def generatorsNLHomotopyEquiv :
    HomotopyEquiv
      (Algebra.Extension.NaiveCotangent.complex (polynomialExtension α hα))
      (Algebra.naiveCotangent A B) :=
  Algebra.Extension.NaiveCotangent.generatorsHomotopyEquiv
    (Algebra.Generators.ofAlgHom α hα) (Algebra.Generators.self A B)

/-- Scalar extension of the presentation-independence homotopy equivalence
from `NL(α)` to the canonical `NL_{B/A}`. -/
private def generatorsScalarExtensionHomotopyEquiv :
    HomotopyEquiv
      (BaseChange.scalarExtension (polynomialExtension α hα) :
        ChainComplex (ModuleCat (algebraCompletion I B)) ℕ)
      (BaseChange.scalarExtension (Algebra.Generators.self A B).toExtension :
        ChainComplex (ModuleCat (algebraCompletion I B)) ℕ) :=
  (ModuleCat.extendScalars (algebraMap B (algebraCompletion I B))).mapHomotopyEquiv
    (generatorsNLHomotopyEquiv α hα)

/-- Extension by zero of the scalar-extended presentation-independence homotopy
equivalence. -/
private def generatorsScalarExtensionExtendHomotopyEquiv :
    HomotopyEquiv
      ((BaseChange.scalarExtension (polynomialExtension α hα) :
          ChainComplex (ModuleCat (algebraCompletion I B)) ℕ).extend
        ComplexShape.embeddingDownNat)
      ((BaseChange.scalarExtension (Algebra.Generators.self A B).toExtension :
          ChainComplex (ModuleCat (algebraCompletion I B)) ℕ).extend
        ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap
    (generatorsScalarExtensionHomotopyEquiv I α hα).hom ComplexShape.embeddingDownNat
  inv := HomologicalComplex.extendMap
    (generatorsScalarExtensionHomotopyEquiv I α hα).inv ComplexShape.embeddingDownNat
  homotopyHomInvId :=
    (Homotopy.ofEq (HomologicalComplex.extendMap_comp
        (generatorsScalarExtensionHomotopyEquiv I α hα).hom
        (generatorsScalarExtensionHomotopyEquiv I α hα).inv
        ComplexShape.embeddingDownNat).symm).trans
      (((generatorsScalarExtensionHomotopyEquiv I α hα).homotopyHomInvId.extend
          ComplexShape.embeddingDownNat).trans
        (Homotopy.ofEq (HomologicalComplex.extendMap_id
            (BaseChange.scalarExtension (polynomialExtension α hα) :
              ChainComplex (ModuleCat (algebraCompletion I B)) ℕ)
            ComplexShape.embeddingDownNat)))
  homotopyInvHomId :=
    (Homotopy.ofEq (HomologicalComplex.extendMap_comp
        (generatorsScalarExtensionHomotopyEquiv I α hα).inv
        (generatorsScalarExtensionHomotopyEquiv I α hα).hom
        ComplexShape.embeddingDownNat).symm).trans
      (((generatorsScalarExtensionHomotopyEquiv I α hα).homotopyInvHomId.extend
          ComplexShape.embeddingDownNat).trans
        (Homotopy.ofEq (HomologicalComplex.extendMap_id
            (BaseChange.scalarExtension (Algebra.Generators.self A B).toExtension :
              ChainComplex (ModuleCat (algebraCompletion I B)) ℕ)
            ComplexShape.embeddingDownNat)))

/-- The derived-extension counit along `B → B^∧` is invertible on `NL_{B/A}`,
because `B → B^∧` is flat. -/
instance derivedExtensionCounit_isIso :
    IsIso
      ((ModuleCat.derivedExtensionComplexCounit
          (algebraMap B (algebraCompletion I B))).app
        ((Algebra.naiveCotangent A B).extend ComplexShape.embeddingDownNat)) :=
  sorry

/-- The derived identification `NL_{B^∧/A}^∧ ≅ NL_{B/A} ⊗^L_B B^∧` in `D(B^∧)`,
assembled from `tensorIso`, scalar-extension normalization, presentation
independence of `NL_{B/A}`, and flat derived-versus-underived base change. -/
@[no_expose] def derivedTensorIso :
    naiveCotangentObject I (completionPresentation I α hα) ≅
      (ModuleCat.derivedExtensionOfScalars
          (algebraMap B (algebraCompletion I B))).obj
        (Algebra.naiveCotangentObject A B) :=
  (DerivedCategory.Q.mapIso
      ((ComplexShape.embeddingDownNat.extendFunctor
          (ModuleCat (algebraCompletion I B))).mapIso
        (tensorIso I α hα))).trans
    ((DerivedCategory.Q.mapIso
        ((ComplexShape.embeddingDownNat.extendFunctor
            (ModuleCat (algebraCompletion I B))).mapIso
          (BaseChange.scalarExtensionIsoTensorModel
            (polynomialExtension α hα)).symm)).trans
      ((derivedIsoOfHomotopyEquiv
          (generatorsScalarExtensionExtendHomotopyEquiv I α hα)).trans
        ((DerivedCategory.Q.mapIso
            (ComplexShape.Embedding.mapAppIso ComplexShape.embeddingDownNat
              (ModuleCat.extendScalars (algebraMap B (algebraCompletion I B)))
              (Algebra.naiveCotangent A B)).symm).trans
          (ModuleCat.DerivedExtension.counitIso
              (algebraMap B (algebraCompletion I B))
              ((Algebra.naiveCotangent A B).extend ComplexShape.embeddingDownNat)
              (derivedExtensionCounit_isIso I)).symm)))

/-- The derived identification is obtained from `tensorIso` by scalar-extension
normalization, presentation independence, and flat derived base change. -/
private theorem derivedTensorIso_of_tensorIso :
    (derivedTensorIso I α hα).hom =
      (DerivedCategory.Q.mapIso
          ((ComplexShape.embeddingDownNat.extendFunctor
              (ModuleCat (algebraCompletion I B))).mapIso
            (tensorIso I α hα))).hom ≫
        ((DerivedCategory.Q.mapIso
            ((ComplexShape.embeddingDownNat.extendFunctor
                (ModuleCat (algebraCompletion I B))).mapIso
              (BaseChange.scalarExtensionIsoTensorModel
                (polynomialExtension α hα)).symm)).hom ≫
          ((derivedIsoOfHomotopyEquiv
              (generatorsScalarExtensionExtendHomotopyEquiv I α hα)).hom ≫
            ((DerivedCategory.Q.mapIso
                (ComplexShape.Embedding.mapAppIso ComplexShape.embeddingDownNat
                  (ModuleCat.extendScalars (algebraMap B (algebraCompletion I B)))
                  (Algebra.naiveCotangent A B)).symm).hom ≫
              (ModuleCat.DerivedExtension.counitIso
                  (algebraMap B (algebraCompletion I B))
                  ((Algebra.naiveCotangent A B).extend ComplexShape.embeddingDownNat)
                  (derivedExtensionCounit_isIso I)).inv))) :=
  sorry

end Algebra.NaiveCotangent.Adic
