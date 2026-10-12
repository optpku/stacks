/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.AtPrime.Locality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness at the closed point

For a local target, its closed point detects global smoothness. This is the single-point form of
the target-locality criterion for smoothness.
@stack 0DQ1
-/

@[expose] public section

universe u v

namespace Algebra.Smooth

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- For a local target, global smoothness is equivalent to smoothness at its closed point. -/
@[stacks 0DQ1 "smoothness at the closed point of a local ring"]
theorem iff_smoothAtPrime_closedPoint [IsLocalRing S] :
    Algebra.Smooth R S ↔
      Algebra.SmoothAtPrime R S (IsLocalRing.closedPoint S) := sorry

end Algebra.Smooth
