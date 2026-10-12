/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Points

/-!
# Points of the site of open sets

This file records elementary fiber calculations for the canonical site point
attached to a point of a topological space.
-/

@[expose] public section

open TopCat

universe u

namespace Opens

variable {X : TopCat.{u}}

/-- Example 7.33.5 (00YE): the canonical point of the opens site has empty fiber over an open
which does not contain the chosen point. -/
@[stacks 00YE]
theorem pointFiber_isEmpty_of_not_mem
    (x : X) (U : TopologicalSpace.Opens X) (hx : x ∉ U) :
    IsEmpty ((pointGrothendieckTopology x).fiber.obj U) := sorry

end Opens
