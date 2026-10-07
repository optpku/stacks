module

public import Mathlib.RingTheory.Henselian
import StacksCheckRecall

/-! @stack 06RR -/

@[expose] public section

universe u

open IsLocalRing Polynomial

/- Lemma 10.153.2: local roots congruent modulo the maximal ideal are equal when the
derivative at one root is a unit. This anonymous specialization preserves the source form
without exporting a second name for the Mathlib uniqueness theorem. -/
@[stacks 06RR "source congruence form"]
#check fun
    {R : Type u} [CommRing R] [IsLocalRing R]
    {f : R[X]} {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hab : a ≡ b [SMOD maximalIdeal R])
    (hder : f.derivative.eval a ∉ maximalIdeal R) =>
  IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub ha.eq_zero hb.eq_zero
    (fun hunit =>
      (notMem_maximalIdeal.mpr hunit) (SModEq.sub_mem.mp hab))
    (notMem_maximalIdeal.mp hder)

@[stacks 06RR "local root uniqueness owner"]
#check @IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
