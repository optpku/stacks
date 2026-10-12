/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Presentation.Basic

@[expose] public section

universe u v w₀ w₁

namespace Module.Relations.Solution

/-- Every relation coefficient vector evaluates to zero on a module solution's generators. -/
theorem sum_var_relation {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    {relations : Module.Relations.{w₀, w₁} R} [Fintype relations.G]
    (solution : relations.Solution M) (r : relations.R) :
    ∑ g, (relations.relation r) g • solution.var g = 0 := sorry

end Module.Relations.Solution
