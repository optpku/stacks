module

public import ReasLib.RingTheory.Module.SupportDim.QuotSMulTop
import StacksCheckRecall

@[expose] public section

/-! @stack 0B52 -/

open IsLocalRing
open Module
open scoped Pointwise

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Lemma 10.63.10 (1): quotienting by an element of the maximal ideal cannot increase support
dimension. -/
@[stacks 0B52 "(1)"]
#check (Module.supportDim_quotSMulTop_le (R := R) (M := M) :
  ∀ (f : R),
    supportDim R (QuotSMulTop f M) ≤ supportDim R M)

/- Lemma 10.63.10 (2): the support dimension drops by at most one. -/
@[stacks 0B52 "(2)"]
#check @Module.supportDim_le_supportDim_quotSMulTop_succ

/- Canonical equality companions remain available from Mathlib through the shared owner. -/
#check @Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
#check @Module.supportDim_quotSMulTop_succ_eq_supportDim

end
