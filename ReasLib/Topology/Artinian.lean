/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sets.Closeds

@[expose] public section

namespace TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A topological space is Artinian when its closed subsets satisfy the ascending chain
condition. -/
abbrev ArtinianSpace (X : Type u) [TopologicalSpace X] : Prop :=
  WellFoundedGT (Closeds X)

/-- A topological space is Artinian if and only if every monotone sequence of closed
subsets is eventually constant. -/
theorem artinianSpace_iff :
    ArtinianSpace X ↔ ∀ Z : ℕ →o Closeds X, ∃ n, ∀ m, n ≤ m → Z n = Z m := sorry

/-- A topological space is Artinian if and only if its open subsets satisfy the descending
chain condition. -/
theorem artinianSpace_iff_wellFoundedLT_opens :
    ArtinianSpace X ↔ WellFoundedLT (Opens X) := sorry

/-- Every finite topological space is Artinian. -/
instance Finite.to_artinianSpace [Finite X] : ArtinianSpace X := sorry

end TopologicalSpace
