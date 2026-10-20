module

public import Mathlib.Topology.NoetherianSpace

@[expose] public section

namespace TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A topological space is Noetherian if and only if every antitone sequence of closed
subsets is eventually constant. -/
theorem noetherianSpace_iff_antitone_closeds :
    NoetherianSpace X ↔ ∀ Z : ℕ → Closeds X, Antitone Z → ∃ n, ∀ m, n ≤ m → Z n = Z m := sorry

end TopologicalSpace
