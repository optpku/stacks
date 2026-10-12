/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.IdealPowerTorsion
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal-adic completion quotients

Every positive principal-power quotient of a ring agrees with the
corresponding quotient of its principal-adic completion.

@stack 0BNJ
-/

@[expose] public section

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- For every positive `n`, the canonical map from `R / (f)^n` to the
corresponding quotient of the `(f)`-adic completion is bijective. -/
@[stacks 0BNJ "principal-adic completion quotient comparison"]
theorem principalPowerQuotientMap_bijective (f : R) (n : ℕ+) :
    Function.Bijective
      (principalPowerIdealImageQuotientMap
        (algebraMap R (principalAdicCompletion f)) f n) := sorry

end AdicCompletion
