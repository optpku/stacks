module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Surjective self-maps of Hausdorff spaces
-/

@[expose] public section

universe u

open Function Set

namespace Continuous

variable {X : Type u} [TopologicalSpace X] [T2Space X] {f : X → X}

/-- A continuous, surjective, nonidentity self-map of a Hausdorff space has a proper closed subset
whose union with its image covers the space. -/
@[stacks 090B "proper closed cover for a nonidentity surjective self-map"]
theorem exists_proper_closed_cover_of_surjective_ne_id
    (hf : Continuous f) (hsurj : Surjective f) (hne : f ≠ id) :
    ∃ E : Set X, IsClosed E ∧ E ≠ univ ∧ E ∪ f '' E = univ := sorry

end Continuous
