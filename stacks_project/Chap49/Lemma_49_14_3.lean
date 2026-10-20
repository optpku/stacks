/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.TraceDifferent
public import ReasLib.RingTheory.DedekindDifferent.Integrality
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry
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

/- Lemma 49.14.3 (1): when the Dedekind different of `A → B` is defined, the
trace-integrality condition is equivalent to `1 ∈ ℒ_{B/A}`. -/
@[stacks 0BWN] #check
  (_root_.dedekindTrace_mem_base_iff_one_mem_complementary
      (A := A) (B := B) h_regular :
    (∀ b : B,
        Algebra.trace (FractionRing A) (B ⊗[A] FractionRing A)
            (algebraMap B (B ⊗[A] FractionRing A) b) ∈
          (algebraMap A (FractionRing A)).range) ↔
      (1 : B ⊗[A] FractionRing A) ∈
        Submodule.dedekindComplementary A (FractionRing A) B
          (B ⊗[A] FractionRing A))

/- Lemma 49.14.3 (2): if `1 ∈ ℒ_{B/A}`, then the fractional Dedekind different
is contained in the canonical copy of `B`. -/
@[stacks 0BWN] #check
  (_root_.dedekindDifferent_le_base_of_one_mem_complementary
      (A := A) (B := B) h_regular :
    ∀ (h_one : (1 : B ⊗[A] FractionRing A) ∈
      Submodule.dedekindComplementary A (FractionRing A) B
        (B ⊗[A] FractionRing A)),
      Submodule.dedekindDifferent A (FractionRing A) B
        (B ⊗[A] FractionRing A) ≤ 1)

/- Lemma 49.14.3 (3): the annihilator of the trace-functional quotient is the
ideal-valued Dedekind different. -/
@[stacks 0BWN] #check
  (Algebra.RelativeDualizingModule.annihilatorDualQuotient_eq_dedekindDifferentIdeal
      (A := A) (B := B) h_regular :
    ∀ (h_one : (1 : B ⊗[A] FractionRing A) ∈
      Submodule.dedekindComplementary A (FractionRing A) B
        (B ⊗[A] FractionRing A)),
      Module.annihilator B
          (Module.Dual A B ⧸ Submodule.span B
            {dedekindComparison A B ⟨1, h_one⟩}) =
        dedekindDifferentIdeal A B)

/- Lemma 49.14.3 (4): the generalized different on `Spec B` is the ideal
sheaf associated to the Dedekind different of `A → B`. -/
@[stacks 0BWN] #check
  (Algebra.RelativeDualizingModule.traceDifferentIdealSheaf_eq_dedekindDifferent
      (A := A) (B := B) h_regular :
    ∀ (h_one : (1 : B ⊗[A] FractionRing A) ∈
      Submodule.dedekindComplementary A (FractionRing A) B
        (B ⊗[A] FractionRing A)),
      Scheme.idealSheafDataOfIdealOnSpec
          (Module.annihilator B
            (Module.Dual A B ⧸ Submodule.span B
              {dedekindComparison A B ⟨1, h_one⟩})) =
        Scheme.idealSheafDataOfIdealOnSpec
          (dedekindDifferentIdeal A B))

end Algebra.RelativeDualizingModule
