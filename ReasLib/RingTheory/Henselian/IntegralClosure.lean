/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import ReasLib.RingTheory.Henselian.Integral
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Integral closures of henselian local rings

Unlike a general integral extension, the target type `integralClosure R S`
determines both its base and ambient domain.  The henselian transfer therefore
has a canonical global instance interface here.

@stack 092X
-/

universe u v

namespace integralClosure

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [Algebra R S]

/-- The integral closure of a henselian local ring in a domain is henselian
local. -/
@[stacks 092X "integral closures of henselian local rings"]
instance instHenselianLocalRing [IsDomain S] [HenselianLocalRing R] :
    HenselianLocalRing (integralClosure R S) := sorry
-- Proof strategy: use `IsIntegralClosure.isIntegral_algebra R S` and specialize
-- `HenselianLocalRing.of_isIntegral` to `integralClosure R S`.

/-- The integral closure of a strictly henselian local ring in a domain is
strictly henselian local. -/
@[stacks 092X "integral closures of strictly henselian local rings"]
instance instStrictHenselianLocalRing [IsDomain S] [StrictHenselianLocalRing R] :
    StrictHenselianLocalRing (integralClosure R S) := sorry
-- Proof strategy: use `IsIntegralClosure.isIntegral_algebra R S` and specialize
-- `StrictHenselianLocalRing.of_isIntegral` to `integralClosure R S`.

end integralClosure
