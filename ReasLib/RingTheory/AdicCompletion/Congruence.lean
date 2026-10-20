module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Congruence in an adic completion

This leaf relates membership in the extended powers of the defining ideal to
equality after evaluation at a finite quotient stage.

@stack 05GG
@stack 0AH5
-/

universe u

namespace AdicCompletion

/-- The extension of `I ^ n` to the `I`-adic completion. -/
@[stacks 0AH5 "extended ideal power in an adic completion"]
noncomputable def extendedIdealPow
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    Ideal (AdicCompletion I R) :=
  Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n)

/-- For a finitely generated ideal, the kernel of evaluation at
the `n`th stage is the image of `I ^ n` in the completion. This direct form
matches quotient and kernel arguments without unfolding `extendedIdealPow`. -/
@[stacks 05GG "adic-completion evaluation kernel"]
theorem map_pow_eq_ker_eval
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ) :
    Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) =
      RingHom.ker (evalₐ I n) := sorry

/-- The kernel of evaluation at the `n`th stage is the extended
`n`th ideal power in the completion. -/
@[stacks 05GG "extended ideal power as an evaluation kernel"]
theorem extendedIdealPow_eq_ker_eval
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ) :
    extendedIdealPow I n = RingHom.ker (evalₐ I n) := sorry

/-- Membership in an extended ideal power is detected by vanishing at the
corresponding finite quotient stage. -/
@[simp, stacks 05GG "extended ideal power membership by evaluation"]
theorem mem_extendedIdealPow_iff_eval_eq_zero
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ)
    (x : AdicCompletion I R) :
    x ∈ extendedIdealPow I n ↔ evalₐ I n x = 0 := sorry

/-- Two elements of an adic completion are congruent modulo an extended ideal
power exactly when they agree at the corresponding finite quotient stage. -/
@[stacks 0AH5 "adic-completion congruence criterion"]
theorem sub_mem_extendedIdealPow_iff_eval_eq
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ)
    (x y : AdicCompletion I R) :
    x - y ∈ extendedIdealPow I n ↔ evalₐ I n x = evalₐ I n y := sorry

/-- Membership of a difference in the extended `n`th ideal power is
equivalent to equality of the two elements at the `n`th quotient stage. -/
@[stacks 0AH5 "adic-completion congruence criterion"]
theorem sub_mem_map_pow_iff_eval_eq
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ)
    (x : AdicCompletion I R) (r : R) :
    x - algebraMap R (AdicCompletion I R) r ∈
        extendedIdealPow I n ↔
      evalₐ I n x = Ideal.Quotient.mk (I ^ n) r := sorry

end AdicCompletion
