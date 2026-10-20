module

public import Mathlib.RingTheory.Etale.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.DedekindDifferent.TraceDual
public import ReasLib.RingTheory.Normal.Ring

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

include h_noetherian h_finite h_regular h_etale

/-- If `B` is flat over `A`, the generic-fibre trace of every element of `B`
belongs to the canonical image of `A` in its total quotient ring. -/
theorem dedekindTrace_mem_base_of_flat [h_flat : Module.Flat A B] :
    ∀ b : B,
      Algebra.trace (FractionRing A) (B ⊗[A] FractionRing A)
          (algebraMap B (B ⊗[A] FractionRing A) b) ∈
        (algebraMap A (FractionRing A)).range := sorry

/-- If `A` is normal, the generic-fibre trace of every element of `B`
belongs to the canonical image of `A` in its total quotient ring. -/
theorem dedekindTrace_mem_base_of_isNormalRing [h_normal : IsNormalRing A] :
    ∀ b : B,
      Algebra.trace (FractionRing A) (B ⊗[A] FractionRing A)
          (algebraMap B (B ⊗[A] FractionRing A) b) ∈
        (algebraMap A (FractionRing A)).range := sorry

/-- Generic-fibre trace integrality for every element of `B` is equivalent to
membership of `1` in the complementary module. -/
theorem dedekindTrace_mem_base_iff_one_mem_complementary :
    (∀ b : B,
        Algebra.trace (FractionRing A) (B ⊗[A] FractionRing A)
            (algebraMap B (B ⊗[A] FractionRing A) b) ∈
          (algebraMap A (FractionRing A)).range) ↔
      (1 : B ⊗[A] FractionRing A) ∈
        Submodule.dedekindComplementary A (FractionRing A) B
          (B ⊗[A] FractionRing A) := sorry

/-- If `1` belongs to the complementary module, the Dedekind different is
contained in the canonical copy of `B` in the generic fibre. -/
theorem dedekindDifferent_le_base_of_one_mem_complementary
    (h_one : (1 : B ⊗[A] FractionRing A) ∈
      Submodule.dedekindComplementary A (FractionRing A) B
        (B ⊗[A] FractionRing A)) :
    Submodule.dedekindDifferent A (FractionRing A) B
      (B ⊗[A] FractionRing A) ≤ 1 := sorry
