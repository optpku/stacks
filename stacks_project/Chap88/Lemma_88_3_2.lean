module

public import stacks_project.Chap88.Lemma_88_3_2_Comparison
public import stacks_project.Chap88.Lemma_88_3_2_Presentation

/-!
# Lemma 88.3.2

The completed naive cotangent complex of the `I`-adic completion of a finite-type
algebra is identified with the tensor of a chosen polynomial presentation, both
as complexes and after derived extension of scalars.
-/

@[expose] public section

noncomputable section

universe u

open Algebra.NaiveCotangent.Adic
open Algebra.Extension.NaiveCotangent.BaseChange
open CategoryTheory

namespace Algebra.NaiveCotangent.Adic

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {B : Type u} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
variable {ι : Type u} [Fintype ι]
variable (I : Ideal A)
variable (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α)

/-- Lemma 88.3.2 (1): Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
Let `A → B` be a finite type ring map. Choose a presentation
`α : A[x_ι] → B`. Then `NL_{B^∧/A}^∧ = NL(α) ⊗_B B^∧` as complexes. The source
`lim` is the termwise completion-as-tensor identification of the finite complex
`NL(α)`, not the inverse system of Lemma 88.3.3. -/
@[stacks 0GAF]
noncomputable abbrev naiveCotangent_iso_tensor :
    naiveCotangent I (completionPresentation I α hα) ≅
      tensorModel (polynomialExtension α hα) :=
  tensorIso I α hα

/-- Unfolding of the complex-level identification of Lemma 88.3.2 (1). -/
theorem naiveCotangent_iso_tensor_eq :
    naiveCotangent_iso_tensor I α hα = tensorIso I α hα :=
  sorry

/-- Lemma 88.3.2 (2): Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
Let `A → B` be a finite type ring map. Choose a presentation
`α : A[x_ι] → B`. Then `NL_{B^∧/A}^∧ = NL_{B/A} ⊗^L_B B^∧` in `D(B^∧)`. -/
@[stacks 0GAF]
noncomputable abbrev naiveCotangentObject_iso_derivedTensor :
    naiveCotangentObject I (completionPresentation I α hα) ≅
      (ModuleCat.derivedExtensionOfScalars
          (algebraMap B (algebraCompletion I B))).obj
        (Algebra.naiveCotangentObject A B) :=
  derivedTensorIso I α hα

/-- Unfolding of the derived identification of Lemma 88.3.2 (2). -/
theorem naiveCotangentObject_iso_derivedTensor_eq :
    naiveCotangentObject_iso_derivedTensor I α hα = derivedTensorIso I α hα :=
  sorry

end Algebra.NaiveCotangent.Adic
