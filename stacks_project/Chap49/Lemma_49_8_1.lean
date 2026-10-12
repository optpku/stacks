/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DedekindDifferent.Integrality
import StacksCheckRecall

@[expose] public section

open scoped Algebra.TensorProduct.Right TensorProduct

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [h_noetherian : IsNoetherianRing A] [h_finite : Module.Finite A B]
variable
  (h_regular : ∀ a ∈ nonZeroDivisors A,
    algebraMap A B a ∈ nonZeroDivisors B)
variable
  [h_etale : Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A)]

section Flat

variable [h_flat : Module.Flat A B]

/- Lemma 49.8.1 (1): flatness of `B` over `A` implies that the generic-fibre trace
of every element of `B` belongs to the canonical image of `A`. -/
@[stacks 0BW1] #check
  (dedekindTrace_mem_base_of_flat (A := A) (B := B) h_regular :
    ∀ b : B,
      Algebra.trace (FractionRing A) (B ⊗[A] FractionRing A)
          (algebraMap B (B ⊗[A] FractionRing A) b) ∈
        (algebraMap A (FractionRing A)).range)

end Flat

section Normal

variable [h_normal : IsNormalRing A]

/- Lemma 49.8.1 (2): normality of `A` implies that the generic-fibre trace
of every element of `B` belongs to the canonical image of `A`. -/
@[stacks 0BW1] #check
  (dedekindTrace_mem_base_of_isNormalRing (A := A) (B := B) h_regular :
    ∀ b : B,
      Algebra.trace (FractionRing A) (B ⊗[A] FractionRing A)
          (algebraMap B (B ⊗[A] FractionRing A) b) ∈
        (algebraMap A (FractionRing A)).range)

end Normal


/- Lemma 49.8.1 (3): generic-fibre trace integrality for every element of `B`
is equivalent to membership of `1` in the complementary module. -/
@[stacks 0BW1] #check
  (dedekindTrace_mem_base_iff_one_mem_complementary
      (A := A) (B := B) h_regular :
    (∀ b : B,
        Algebra.trace (FractionRing A) (B ⊗[A] FractionRing A)
            (algebraMap B (B ⊗[A] FractionRing A) b) ∈
          (algebraMap A (FractionRing A)).range) ↔
      (1 : B ⊗[A] FractionRing A) ∈
        Submodule.dedekindComplementary A (FractionRing A) B
          (B ⊗[A] FractionRing A))

/- Lemma 49.8.1 (4): membership of `1` in the complementary module implies
that the Dedekind different is contained in the canonical copy of `B`. -/
@[stacks 0BW1] #check
  (dedekindDifferent_le_base_of_one_mem_complementary
      (A := A) (B := B) h_regular :
    (1 : B ⊗[A] FractionRing A) ∈
        Submodule.dedekindComplementary A (FractionRing A) B
          (B ⊗[A] FractionRing A) →
      Submodule.dedekindDifferent A (FractionRing A) B
        (B ⊗[A] FractionRing A) ≤ 1)
