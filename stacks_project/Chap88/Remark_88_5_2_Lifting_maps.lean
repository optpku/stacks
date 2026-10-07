module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»
public import stacks_project.Chap88.Remark_88_5_2_Lifting_maps_Improve
public import stacks_project.Chap88.Remark_88_5_2_Lifting_maps_Obstruction

/-!
# Lifting maps along adic quotients

If the obstruction class of `ψn` maps to zero after a size-conditioned coefficient
change `n > n' > n/2`, then `ψn` lifts to an algebra map into `C ⧸ I^{2n'} C`
agreeing on `C ⧸ I^{n'} C`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra.NaiveCotangent.Adic

namespace Algebra.NaiveCotangent.Adic

variable {A B C ι : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]

/-- Remark 88.5.2 (Lifting maps): Let `A` be a Noetherian ring and `I ⊂ A` an
ideal. Let `B` be an object of (88.2.0.2) and let `C` be an `I`-adically complete
`A`-algebra. Given a completed presentation `P` of `B`, a map
`ψn : B →ₐ[A] C ⧸ I^n C`, a lift `ψ` of `ψn` to `A[x_ι]^∧`, and integers
`n > n' > n/2`, if the obstruction class `o(ψn)` maps to zero in
`Ext¹_B(NL_{B/A}^∧, I^{n'} C / I^{2n'} C)`, then there is an `A`-algebra map
`ψ'_{2n'} : B →ₐ[A] C ⧸ I^{2n'} C` agreeing with `ψn` as maps into
`C ⧸ I^{n'} C`. -/
@[stacks 0GAP]
theorem exists_hom_of_map_obstructionClass_eq_zero [IsNoetherianRing A]
    {I : Ideal A} [Algebra.TopologicallyFiniteType I B]
    [IsAdicComplete (I.map (algebraMap A C)) C] [Fintype ι]
    (P : Presentation A B I ι) {n n' : ℕ} (hn : n' < n) (hhalf : n < 2 * n')
    (ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ)
    (hobs : map_obstructionClass hn.le hψ = 0) :
    ∃ ψ' : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n'),
      (Ideal.Quotient.factorₐ A
            (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n' zero_lt_two))).comp ψ' =
        (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn.le)).comp ψn :=
  sorry

/-- The extreme case `n' = n` of the lifting criterion: vanishing of `o(ψn)` in
`Ext¹_B(NL_{B/A}^∧, I^n C / I^{2n} C)` is the obstruction to lifting `ψn` to
`C ⧸ I^{2n} C` while remaining equal to `ψn` on `C ⧸ I^n C`. -/
theorem exists_hom_of_obstructionClass_eq_zero [IsNoetherianRing A]
    {I : Ideal A} [Algebra.TopologicallyFiniteType I B]
    [IsAdicComplete (I.map (algebraMap A C)) C] [Fintype ι]
    (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ)
    (hobs : obstructionClass hψ = 0) :
    ∃ ψ' : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n),
      (Ideal.Quotient.factorₐ A
            (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n zero_lt_two))).comp ψ' =
        ψn :=
  sorry

end Algebra.NaiveCotangent.Adic
