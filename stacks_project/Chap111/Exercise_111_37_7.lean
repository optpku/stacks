/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_37_7_Weights12
public import stacks_project.Chap111.Exercise_111_37_7_Weights123
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Proj.Weights123

/-- Exercise 111.37.7 (1): for the weighted polynomial ring `k[x, y, z]` with weights `1`, `2`,
and `3`, writing `X = Proj(R)`, the canonical twist `𝒪_X(1)` is not an invertible `𝒪_X`-module. -/
@[stacks 02A3]
theorem twistOne_not_invertible (k : Type u) [Field k] :
    ¬ Invertible (twist k 1) := sorry

end AlgebraicGeometry.Proj.Weights123

namespace AlgebraicGeometry.Proj.Weights12

/-- Exercise 111.37.7 (2): for the weighted polynomial ring `k[x, y]` with weights `1` and `2`,
writing `X = Proj(R)`, the canonical twist `𝒪_X(1)` is invertible, but the natural multiplication
`𝒪_X(1) ⊗ 𝒪_X(1) ⟶ 𝒪_X(2)` is not an isomorphism. -/
@[stacks 02A3]
theorem twistOne_invertible_mul_not_iso (k : Type u) [Field k] :
    Invertible (twist k 1) ∧ ¬ IsIso (mulOneOne k) := sorry

end AlgebraicGeometry.Proj.Weights12
