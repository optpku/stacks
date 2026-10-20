/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Lifting
import StacksCheckRecall

universe u

open Algebra.NaiveCotangent.Adic

/- Remark 88.5.2 (Lifting maps): Let `A` be a Noetherian ring and `I ⊂ A` an
ideal. Let `B` be an object of (88.2.0.2) and let `C` be an `I`-adically complete
`A`-algebra. Given a completed presentation `P` of `B`, a map
`ψn : B →ₐ[A] C ⧸ I^n C`, a lift `ψ` of `ψn` to `A[x_ι]^∧`, and integers
`n > n' > n/2`, if the obstruction class `o(ψn)` maps to zero in
`Ext¹_B(NL_{B/A}^∧, I^{n'} C / I^{2n'} C)`, then there is an `A`-algebra map
`ψ'_{2n'} : B →ₐ[A] C ⧸ I^{2n'} C` agreeing with `ψn` as maps into
`C ⧸ I^{n'} C`. -/
@[stacks 0GAP]
#check (Algebra.NaiveCotangent.Adic.exists_hom_of_map_obstructionClass_eq_zero :
    ∀ {A B C ι : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing A]
    {I : Ideal A} [Algebra.TopologicallyFiniteType I B]
    [IsAdicComplete (I.map (algebraMap A C)) C] [Fintype ι]
    (P : Presentation A B I ι) {n n' : ℕ} (hn : n' < n) (hhalf : n < 2 * n')
    (ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ)
    (hobs : map_obstructionClass hn.le hψ = 0),
    ∃ ψ' : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n'),
      (Ideal.Quotient.factorₐ A
            (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n' zero_lt_two))).comp ψ' =
        (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn.le)).comp ψn)

/- The equal-index case lifts the original residue map without a strict size condition. -/
#check (Algebra.NaiveCotangent.Adic.exists_hom_of_obstructionClass_eq_zero :
    ∀ {A B C ι : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing A]
    {I : Ideal A} [Algebra.TopologicallyFiniteType I B]
    [IsAdicComplete (I.map (algebraMap A C)) C] [Fintype ι]
    (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ)
    (hobs : obstructionClass hψ = 0),
    ∃ ψ' : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n),
      (Ideal.Quotient.factorₐ A
            (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n zero_lt_two))).comp ψ' =
        ψn)
