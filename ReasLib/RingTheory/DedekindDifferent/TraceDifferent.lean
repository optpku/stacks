/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DedekindDifferent.Comparison
public import ReasLib.RingTheory.DedekindDifferent.Ideal

@[expose] public section

noncomputable section

open scoped Algebra.DualModule Algebra.TensorProduct.Right TensorProduct

universe u

namespace Algebra.RelativeDualizingModule

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [h_noetherian : IsNoetherianRing A] [h_finite : Module.Finite A B]
variable
  (h_regular : ∀ a ∈ nonZeroDivisors A,
    algebraMap A B a ∈ nonZeroDivisors B)
variable
  [h_etale : Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A)]

include h_noetherian h_finite h_regular h_etale

/-- The annihilator of the quotient by the trace functional associated to `1` in
the complementary module is the ideal-valued Dedekind different. -/
theorem annihilatorDualQuotient_eq_dedekindDifferentIdeal
    (h_one : (1 : B ⊗[A] FractionRing A) ∈
      Submodule.dedekindComplementary A (FractionRing A) B
        (B ⊗[A] FractionRing A)) :
    Module.annihilator B
        (Module.Dual A B ⧸ Submodule.span B
          {dedekindComparison A B ⟨1, h_one⟩}) =
      dedekindDifferentIdeal A B := sorry

end Algebra.RelativeDualizingModule
