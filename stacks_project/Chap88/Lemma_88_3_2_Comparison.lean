/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
public import stacks_project.Chap88.Definition_88_8_1_Derived
public import stacks_project.Chap88.Lemma_88_3_2_Presentation

/-!
# Comparison of completed naive cotangent complexes with tensor base change

This leaf identifies the completed Jacobian complex of the completed presentation
of `B^∧` with the two-term tensor model of `NL(α)`, and compares the resulting
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
/-- The polynomial ring of `α` is a module over `A[x_ι]`. -/
instance instPolynomialExtension_ring_module :
    Module (MvPolynomial ι A) (polynomialExtension α hα).Ring :=
  inferInstanceAs
    (Module (polynomialExtension α hα).Ring (polynomialExtension α hα).Ring)

variable (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) in
/-- `A[x_ι]` is a finite module over itself. -/
instance instPolynomialExtension_ring_finite :
    Module.Finite (MvPolynomial ι A) (polynomialExtension α hα).Ring :=
  inferInstanceAs (Module.Finite (MvPolynomial ι A) (MvPolynomial ι A))

variable (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) in
/-- The polynomial ring of `α` acts on the kernel of `α`. -/
instance instPolynomialExtension_ker_module :
    Module (MvPolynomial ι A) (polynomialExtension α hα).ker :=
  inferInstanceAs
    (Module (polynomialExtension α hα).Ring (polynomialExtension α hα).ker)

variable (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) in
/-- The polynomial ring of `α` acts on the conormal module `J / J²`. -/
instance instPolynomialExtension_cotangent_module :
    Module (MvPolynomial ι A) (polynomialExtension α hα).Cotangent :=
  inferInstanceAs
    (Module (polynomialExtension α hα).Ring (polynomialExtension α hα).Cotangent)

variable (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) in
/-- The `A`-action on `J / J²` factors through `A[x_ι]`. -/
instance instPolynomialExtension_cotangent_isScalarTower :
    IsScalarTower A (MvPolynomial ι A) (polynomialExtension α hα).Cotangent :=
  inferInstanceAs
    (IsScalarTower A (polynomialExtension α hα).Ring
      (polynomialExtension α hα).Cotangent)

variable (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) in
/-- The inclusion of `J = ker(α)` into `A[x_ι]`. -/
def polynomialKerSubtype :
    (polynomialExtension α hα).ker →ₗ[MvPolynomial ι A] MvPolynomial ι A :=
  (polynomialExtension α hα).ker.subtype

variable (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) in
/-- The inclusion of `J` is the subtype coercion. -/
theorem polynomialKerSubtype_apply (x : (polynomialExtension α hα).ker) :
    polynomialKerSubtype α hα x = x.val :=
  sorry

variable (I : Ideal A)
variable (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α)

/-- The kernel of a finite-type presentation over a Noetherian ring is finitely
generated, so the conormal module `J / J²` is a finite `B`-module. -/
theorem polynomialExtension_cotangent_finite :
    Module.Finite B (polynomialExtension α hα).Cotangent :=
  sorry

/-- Degree-zero finite-free identification `B^∧ ⊗_B (ι → B) ≃ (ι → B^∧)`. -/
def freeTensorEquiv :
    algebraCompletion I B ⊗[B] (ι → B) ≃ₗ[algebraCompletion I B]
      (ι → algebraCompletion I B) :=
  open Classical in
    TensorProduct.piScalarRight B (algebraCompletion I B) (algebraCompletion I B) ι

/-- Evaluating the finite-free tensor identification on elementary tensors. -/
theorem freeTensorEquiv_tmul (x : algebraCompletion I B) (f : ι → B) :
    freeTensorEquiv I (x ⊗ₜ f) = fun i ↦ f i • x :=
  sorry

/-- The canonical finite-free identification of the cotangent space of `α`
with the free module on the variables. -/
def cotangentSpaceFunEquiv :
    (polynomialExtension α hα).CotangentSpace ≃ₗ[B] (ι → B) :=
  (Algebra.Generators.ofAlgHom α hα).cotangentSpaceBasis.equivFun

/-- Degree-zero identification `B^∧ ⊗_B Ω(α) ≃ (ι → B^∧)`. -/
def freeCotangentSpaceEquiv :
    algebraCompletion I B ⊗[B] (polynomialExtension α hα).CotangentSpace ≃ₗ[algebraCompletion I B]
      (ι → algebraCompletion I B) :=
  (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (algebraCompletion I B) (algebraCompletion I B))
      (cotangentSpaceFunEquiv α hα)).trans
    (freeTensorEquiv I)

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
theorem kerCompletion_range_eq :
    LinearMap.range
        (AdicCompletion.map (polynomialIdeal A I ι)
          (polynomialKerSubtype α hα)) =
      (completionPresentation I α hα).ker :=
  sorry

/-- Identification of `ker(completionAlgHom)` with the `I A[x_ι]`-adic
completion of `J = ker(α)`. -/
def kerCompletionEquiv :
    AdicCompletion (polynomialIdeal A I ι) (polynomialExtension α hα).ker
      ≃ₗ[polynomialCompletion A I ι]
      (completionPresentation I α hα).ker :=
  (LinearEquiv.ofInjective
      (AdicCompletion.map (polynomialIdeal A I ι)
        (polynomialKerSubtype α hα))
      (AdicCompletion.map_injective (polynomialIdeal A I ι)
        (polynomialExtension α hα).ker.injective_subtype)).trans
    (LinearEquiv.ofEq _ _ (kerCompletion_range_eq I α hα))

/-- The identification of kernels extends the completed inclusion of `J`. -/
theorem kerCompletionEquiv_subtype
    (x : AdicCompletion (polynomialIdeal A I ι) (polynomialExtension α hα).ker) :
    (kerCompletionEquiv I α hα x : polynomialCompletion A I ι) =
      AdicCompletion.map (polynomialIdeal A I ι)
        (polynomialKerSubtype α hα) x :=
  sorry

/-- Each finite adic stage of `J / J²` as an `A[x_ι]`-module is contained in
the corresponding stage as a `B`-module. -/
theorem cotangentStageSubmodule_le (n : ℕ) :
    ((polynomialIdeal A I ι ^ n • ⊤ :
          Submodule (MvPolynomial ι A)
            (polynomialExtension α hα).Cotangent).restrictScalars A) ≤
      (((I.map (algebraMap A B)) ^ n • ⊤ :
          Submodule B (polynomialExtension α hα).Cotangent).restrictScalars A) :=
  sorry

/-- The comparison of finite adic stages of `J / J²` along `A[x_ι]` and along `B`. -/
def cotangentStageFactor (n : ℕ) :
    (polynomialExtension α hα).Cotangent ⧸
        (polynomialIdeal A I ι ^ n • ⊤ :
          Submodule (MvPolynomial ι A) (polynomialExtension α hα).Cotangent) →ₗ[A]
      (polynomialExtension α hα).Cotangent ⧸
        ((I.map (algebraMap A B)) ^ n • ⊤ :
          Submodule B (polynomialExtension α hα).Cotangent) :=
  (Submodule.Quotient.restrictScalarsEquiv A
      ((I.map (algebraMap A B)) ^ n • ⊤ :
        Submodule B (polynomialExtension α hα).Cotangent)).toLinearMap ∘ₗ
    Submodule.factor (cotangentStageSubmodule_le I α hα n) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv A
          (polynomialIdeal A I ι ^ n • ⊤ :
            Submodule (MvPolynomial ι A)
              (polynomialExtension α hα).Cotangent)).symm.toLinearMap

/-- Completing `J / J²` as an `A[x_ι]`-module along `I A[x_ι]` compares with
completing it as a `B`-module along `I B`. -/
def cotangentAdicChangeOfRing :
    AdicCompletion (polynomialIdeal A I ι) (polynomialExtension α hα).Cotangent
      →ₗ[A]
      AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent where
  toFun x :=
    ⟨fun n ↦ cotangentStageFactor I α hα n
        (AdicCompletion.eval (polynomialIdeal A I ι)
          (polynomialExtension α hα).Cotangent n x),
      fun _ ↦ sorry⟩
  map_add' := sorry
  map_smul' := sorry

/-- Evaluating the change-of-rings comparison of completed conormals at a finite
adic stage recovers `cotangentStageFactor`. -/
theorem cotangentAdicChangeOfRing_eval (n : ℕ)
    (x : AdicCompletion (polynomialIdeal A I ι) (polynomialExtension α hα).Cotangent) :
    (cotangentAdicChangeOfRing I α hα x).val n =
      cotangentStageFactor I α hα n
        (AdicCompletion.eval (polynomialIdeal A I ι)
          (polynomialExtension α hα).Cotangent n x) :=
  sorry

/-- Completing the quotient `J → J / J²` after identifying
`ker(completionAlgHom)` with the completion of `J`. -/
def presentationKerToCotangentCompletion :
    ((completionPresentation I α hα).ker).restrictScalars A →ₗ[A]
      AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent where
  toFun y :=
    cotangentAdicChangeOfRing I α hα
      (AdicCompletion.map (polynomialIdeal A I ι)
        (Cotangent.mk :
            (polynomialExtension α hα).ker →ₗ[(polynomialExtension α hα).Ring]
              (polynomialExtension α hα).Cotangent)
        ((kerCompletionEquiv I α hα).symm
          ⟨(y : polynomialCompletion A I ι), y.2⟩))
  map_add' := sorry
  map_smul' := sorry

/-- Inverse of `cotangentCompletionHom`: complete `J → J / J²` after identifying
`ker(completionAlgHom)` with the completion of `ker(α)`. `B^∧`-linearity is
deferred. -/
def cotangentCompletionHomInv :
    (completionPresentation I α hα).toExtension.Cotangent
      →ₗ[algebraCompletion I B]
      AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent where
  toFun x :=
    Submodule.liftQ
      (((completionPresentation I α hα).ker • ⊤ :
            Submodule (polynomialCompletion A I ι)
              (completionPresentation I α hα).ker).restrictScalars A)
      (presentationKerToCotangentCompletion I α hα) sorry
      ((Submodule.Quotient.restrictScalarsEquiv A
          ((completionPresentation I α hα).ker • ⊤ :
            Submodule (polynomialCompletion A I ι)
              (completionPresentation I α hα).ker)).symm
        (Algebra.Extension.Cotangent.val x))
  map_add' := sorry
  map_smul' := sorry

/-- Degree-one identification `(J / J²)^∧ ≃ J^∧ / (J^∧)²`. Both directions are
explicit completed-conormal maps; inverse laws are deferred. -/
def cotangentCompletionEquiv :
    AdicCompletion (I.map (algebraMap A B)) (polynomialExtension α hα).Cotangent
      ≃ₗ[algebraCompletion I B]
      (completionPresentation I α hα).toExtension.Cotangent :=
  LinearEquiv.ofLinear (cotangentCompletionHom I α hα)
    (cotangentCompletionHomInv I α hα) sorry sorry

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

/-- The degree-one completion-as-tensor factor is
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`. -/
theorem cotangentTensorCompletionEquiv_eq :
    cotangentTensorCompletionEquiv I α hα =
      @AdicCompletion.ofTensorProductEquivOfFiniteNoetherian B _ (I.map (algebraMap A B))
        (polynomialExtension α hα).Cotangent _ _
        (Algebra.FiniteType.isNoetherianRing A B)
        (Cotangent.finite
          ((isNoetherianRing_iff_ideal_fg (R := MvPolynomial ι A)).mp inferInstance
            (polynomialExtension α hα).ker)) :=
  rfl

/-- Specification of the degree-one identification as the unique `B^∧`-linear
extension of the conormal map of `polynomialToCompletionHom`. -/
theorem cotangentTensorEquiv_spec :
    (cotangentTensorEquiv I α hα).toLinearMap = cotangentTensorHom I α hα :=
  sorry

/-- Degree-zero component of the complex identification
`NL_{B^∧/A}^∧ ≅ NL(α) ⊗_B B^∧`. -/
def tensorIsoComponentZero :
    (naiveCotangent I (completionPresentation I α hα)).X 0 ≅
      (BaseChange.tensorModel (polynomialExtension α hα)).X 0 :=
  (componentZeroIso (completionPresentation I α hα)).trans
    (freeCotangentSpaceEquiv I α hα).symm.toModuleIso

/-- Degree-one component of the complex identification
`NL_{B^∧/A}^∧ ≅ NL(α) ⊗_B B^∧`. -/
def tensorIsoComponentOne :
    (naiveCotangent I (completionPresentation I α hα)).X 1 ≅
      (BaseChange.tensorModel (polynomialExtension α hα)).X 1 :=
  (componentOneIso (completionPresentation I α hα)).trans
    (cotangentTensorEquiv I α hα).symm.toModuleIso

/-- Higher components of the completed Jacobian complex are the zero object
of `ModuleCat`. -/
def naiveCotangentComponentSuccIsoUnit (n : ℕ) :
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
def tensorModelComponentSuccIsoUnit (n : ℕ) :
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
def tensorIsoComponentSucc (n : ℕ) :
    (naiveCotangent I (completionPresentation I α hα)).X (n + 2) ≅
      (BaseChange.tensorModel (polynomialExtension α hα) :
          ChainComplex (ModuleCat (algebraCompletion I B)) ℕ).X (n + 2) :=
  (naiveCotangentComponentSuccIsoUnit I α hα n).trans
    (tensorModelComponentSuccIsoUnit I α hα n).symm

/-- Components of the complex identification in every homological degree. -/
def tensorIsoComponent :
    ∀ n : ℕ,
      (naiveCotangent I (completionPresentation I α hα)).X n ≅
        (BaseChange.tensorModel (polynomialExtension α hα)).X n
  | 0 => tensorIsoComponentZero I α hα
  | 1 => tensorIsoComponentOne I α hα
  | n + 2 => tensorIsoComponentSucc I α hα n

/-- The componentwise identification commutes with differentials. -/
theorem tensorIsoComponent_comm (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (tensorIsoComponent I α hα i).hom ≫
        (BaseChange.tensorModel (polynomialExtension α hα)).d i j =
      (naiveCotangent I (completionPresentation I α hα)).d i j ≫
        (tensorIsoComponent I α hα j).hom :=
  sorry

/-- The completed naive cotangent complex of the completed presentation of `B^∧`
is isomorphic to the two-term tensor model of `NL(α)`. The source `lim` is this
termwise identification of the finite complex `NL(α)` with its completion, not
the inverse system of Lemma 88.3.3. -/
def tensorIso :
    naiveCotangent I (completionPresentation I α hα) ≅
      BaseChange.tensorModel (polynomialExtension α hα) :=
  HomologicalComplex.Hom.isoOfComponents (tensorIsoComponent I α hα)
    (tensorIsoComponent_comm I α hα)

/-- The degree-zero component of `tensorIso` is `tensorIsoComponentZero`. -/
theorem tensorIso_X_zero :
    (tensorIso I α hα).hom.f 0 = (tensorIsoComponentZero I α hα).hom :=
  sorry

/-- The degree-one component of `tensorIso` is `tensorIsoComponentOne`. -/
theorem tensorIso_X_one :
    (tensorIso I α hα).hom.f 1 = (tensorIsoComponentOne I α hα).hom :=
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

/-- Derived-category isomorphism induced by a homotopy equivalence of cochain
complexes. -/
def derivedIsoOfHomotopyEquiv
    {T : Type u} [CommRing T] {K L : CochainComplex (ModuleCat T) ℤ}
    (h : HomotopyEquiv K L) :
    DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L where
  hom := DerivedCategory.Q.map h.hom
  inv := DerivedCategory.Q.map h.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Presentation-independence homotopy equivalence from `NL(α)` to the canonical
`NL_{B/A}`. -/
def generatorsNLHomotopyEquiv :
    HomotopyEquiv
      (Algebra.Extension.NaiveCotangent.complex (polynomialExtension α hα))
      (Algebra.naiveCotangent A B) :=
  Algebra.Extension.NaiveCotangent.generatorsHomotopyEquiv
    (Algebra.Generators.ofAlgHom α hα) (Algebra.Generators.self A B)

/-- Scalar extension of the presentation-independence homotopy equivalence
from `NL(α)` to the canonical `NL_{B/A}`. -/
def generatorsScalarExtensionHomotopyEquiv :
    HomotopyEquiv
      (BaseChange.scalarExtension (polynomialExtension α hα) :
        ChainComplex (ModuleCat (algebraCompletion I B)) ℕ)
      (BaseChange.scalarExtension (Algebra.Generators.self A B).toExtension :
        ChainComplex (ModuleCat (algebraCompletion I B)) ℕ) :=
  (ModuleCat.extendScalars (algebraMap B (algebraCompletion I B))).mapHomotopyEquiv
    (generatorsNLHomotopyEquiv α hα)

/-- Extension by zero of the scalar-extended presentation-independence homotopy
equivalence. -/
def generatorsScalarExtensionExtendHomotopyEquiv :
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
theorem derivedExtensionCounit_isIso :
    IsIso
      ((ModuleCat.derivedExtensionComplexCounit
          (algebraMap B (algebraCompletion I B))).app
        ((Algebra.naiveCotangent A B).extend ComplexShape.embeddingDownNat)) :=
  sorry

/-- The derived identification `NL_{B^∧/A}^∧ ≅ NL_{B/A} ⊗^L_B B^∧` in `D(B^∧)`,
assembled from `tensorIso`, scalar-extension normalization, presentation
independence of `NL_{B/A}`, and flat derived-versus-underived base change. -/
def derivedTensorIso :
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
theorem derivedTensorIso_of_tensorIso :
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
