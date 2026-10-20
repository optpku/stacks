module

public import ReasLib.RingTheory.IntegralClosure.Pi
import StacksCheckRecall

@[expose] public section

universe u v w

/-!
# Integral closure in finite products

Lemma 10.36.10 (Tag 0CY9) is a canonical recall of the dependent-product
integral-closure API.  The reusable declarations live in
`ReasLib.RingTheory.IntegralClosure.Pi`; no numbered chapter owns their proofs.
@stack 0CY9
-/

/- Lemma 10.36.10 (1): membership in the integral closure of a finite product
is equivalent to componentwise membership. -/
@[stacks 0CY9]
#check @mem_integralClosure_pi_iff

/- Lemma 10.36.10 (2): a finite product algebra is integrally closed exactly
when every component algebra is integrally closed.  The canonical owner keeps
the same finite-index hypothesis needed for a uniform integral equation. -/
@[stacks 0CY9]
#check @isIntegrallyClosedIn_pi_iff

#check @Pi.algebraMap_forall_apply
#check @IsIntegral.pi_iff
#check @IsIntegral.pi_iff_of_constant
#print axioms isIntegrallyClosedIn_pi_iff
