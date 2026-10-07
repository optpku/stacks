module

public import Mathlib.Topology.Sets.OpenCover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Open covers by a pair of opens

This module owns the `Bool`-indexed family associated to two opens and the criterion that it
covers the ambient space.

@stack 05EV
-/

@[expose] public section

open TopologicalSpace
open TopologicalSpace.Opens

universe u

namespace TopologicalSpace.OpenCover

variable {X : Type u} [TopologicalSpace X]

/-- The `Bool`-indexed family whose members are the opens `U` and `V`. -/
@[stacks 05EV "two-member family of opens"]
def pair (U V : Opens X) : Bool → Opens X
  | false => U
  | true => V

/-- Two opens form an open cover when their supremum is the top open. -/
@[stacks 05EV "two-member open-cover criterion"]
theorem pair_isOpenCover {U V : Opens X} (hcover : U ⊔ V = ⊤) :
    IsOpenCover (pair U V) := sorry

end TopologicalSpace.OpenCover
