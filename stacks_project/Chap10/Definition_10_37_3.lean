/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.IntegralClosure.Complete
import StacksCheckRecall

@[expose] public section

/-!
Definition 10.37.3 (Tag 00GW): complete normality is recalled through the
canonical `completeIntegralClosure` subalgebra; the bottom criterion and its
integrally-closed consequence are reusable views in `CompleteIntegralClosure`.

@stack 00GW
-/
@[stacks 00GW]
#check @IsAlmostIntegral
@[stacks 00GW "complete integral closure"]
#check @completeIntegralClosure

@[stacks 00GW]
#check @CompleteIntegralClosure.eq_bot_iff
#check @CompleteIntegralClosure.isIntegrallyClosed_of_eq_bot

universe u v

section

variable {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/- The source-facing specialization is over a domain and its fraction field;
the owner above is deliberately more general in the ambient algebra. -/
@[stacks 00GW]
#check (CompleteIntegralClosure.eq_bot_iff (R := R) (S := K) :
  completeIntegralClosure R K = ⊥ ↔
    ∀ x : K, IsAlmostIntegral R x → ∃ y : R, algebraMap R K y = x)

@[stacks 00GW]
#check (CompleteIntegralClosure.isIntegrallyClosed_of_eq_bot (R := R) (K := K) :
  completeIntegralClosure R K = ⊥ → IsIntegrallyClosed R)

end
