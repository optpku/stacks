/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Jacobson.Semilocal
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.35.8
@stack 00G5

The example is exposed through its three useful consequences.  The finite-product
and Jacobson-radical arguments are proof-stage infrastructure; the public chapter
surface keeps the source-facing propositions and points to the existing ideal and
local-ring APIs below.
-/

/- Example 10.35.8: a domain with finitely many maximal ideals is not a Jacobson ring unless it
is a field. -/
@[stacks 00G5 "finite maximal spectrum consequence"]
#check @not_isJacobsonRing_of_finite_maximalSpectrum_of_not_isField

/- Example 10.35.8: a local ring with a prime ideal distinct from its maximal ideal is not a
Jacobson ring. -/
@[stacks 00G5 "local-ring consequence"]
#check @IsLocalRing.not_isJacobsonRing_of_exists_prime_ne_maximalIdeal

/- Example 10.35.8: a discrete valuation ring is not a Jacobson ring. -/
@[stacks 00G5 "discrete-valuation-ring consequence"]
#check @IsDiscreteValuationRing.not_isJacobsonRing

@[stacks 00G5 "Jacobson radical of a finite maximal spectrum"]
#check @Ring.jacobson_eq_sInf_isMaximal

@[stacks 00G5 "local Jacobson radical"]
#check @IsLocalRing.jacobson_eq_maximalIdeal

@[stacks 00G5 "DVR nonfield API"]
#check @IsDiscreteValuationRing.not_a_field

end
