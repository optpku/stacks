/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
public import ReasLib.AlgebraicTopology.SimplicialSet.Dimension
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 018O

# Dimension bounds for simplicial skeletons

The left Kan extension of a truncated simplicial set has no nondegenerate simplices above the
truncation degree. The class-valued dimension bound is the canonical reusable statement; the
pointwise degeneracy theorem is its source-facing elimination rule.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

universe u

namespace SSet.Truncated

/-- Extending an `m`-truncated simplicial set by the skeleton left adjoint produces a simplicial
set of dimension at most `m`. -/
@[stacks 018O "dimension of the left extension of a truncated simplicial set"]
instance sk.hasDimensionLE {m : ℕ} (U : SSet.Truncated.{u} m) :
    ((Truncated.sk m).obj U).HasDimensionLE m := sorry

/-- Every simplex above degree `m` in the left extension of an `m`-truncated simplicial set is
degenerate. -/
@[stacks 018O]
theorem sk.mem_degenerate_of_lt {m : ℕ} (U : SSet.Truncated.{u} m)
    {n : ℕ} (h : m < n)
    (x : ((Truncated.sk m).obj U) _⦋n⦌) :
    x ∈ ((Truncated.sk m).obj U).degenerate n := sorry

/-- Every left extension of a truncated simplicial set is eventually degenerate. -/
@[stacks 018O "skeleton eventual degeneracy"]
instance sk.eventuallyDegenerate {m : ℕ} (U : SSet.Truncated.{u} m) :
    ((Truncated.sk m).obj U).EventuallyDegenerate := sorry

end SSet.Truncated

namespace SSet

/-- The full `n`-skeleton has dimension at most `n`.  This low-priority presentation bridge
exposes the primary truncated-skeleton instance through Mathlib's bundled `SSet.sk`. -/
@[instance 40, stacks 017T "full skeleton dimension bound"]
theorem sk.hasDimensionLE (n : ℕ) (U : SSet.{u}) :
    ((sk n).obj U).HasDimensionLE n := sorry

/-- Every simplicial skeleton is eventually degenerate. -/
@[instance 40, stacks 017T "skeleton eventual degeneracy"]
theorem sk.eventuallyDegenerate (n : ℕ) (U : SSet.{u}) :
    ((sk n).obj U).EventuallyDegenerate := sorry

end SSet
