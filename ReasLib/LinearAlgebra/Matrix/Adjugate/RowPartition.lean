/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Adjugates and row partitions

This leaf isolates the matrix identities behind the row-partitioned determinant
trick. Two primitive statements are paired with their canonical `toRows`
views. All use arbitrary finite column indices; the lower row family has no
finiteness or decidable-equality requirement.
-/

@[expose] public section

universe u v w

namespace Matrix

variable {R : Type u} [CommRing R]
variable {ι : Type v} {κ : Type w} [Fintype ι] [DecidableEq ι]

/-- A coordinate of a row vector multiplied by an adjugate is the determinant obtained by
replacing the corresponding row. -/
@[stacks 080R "row replacement by an adjugate"]
theorem vecMul_adjugate_apply (A : Matrix ι ι R) (v : ι → R) (j : ι) :
    (v ᵥ* A.adjugate) j = (A.updateRow j v).det := sorry

/-- The lower-block specialization of `vecMul_adjugate_apply` for an arbitrary
row-partitioned matrix. -/
@[stacks 080R "lower row-partition block by an adjugate"]
theorem toRows₂_mul_adjugate_apply (A : Matrix (ι ⊕ κ) ι R) (i : κ) (j : ι) :
    (A.toRows₂ * A.toRows₁.adjugate) i j =
      (A.toRows₁.updateRow j (A.toRows₂ i)).det := sorry

/-- Multiplying a row-partitioned matrix by the adjugate of its square top block scales the top
block by its determinant and applies the same adjugate to every lower row. -/
@[stacks 080R "row-partitioned adjugate identity"]
theorem fromRows_mul_adjugate (A₁ : Matrix ι ι R) (A₂ : Matrix κ ι R) :
    fromRows A₁ A₂ * A₁.adjugate =
      fromRows (A₁.det • 1) (A₂ * A₁.adjugate) := sorry

/-- The `toRows` view of `fromRows_mul_adjugate` for an arbitrary row-partitioned matrix. -/
@[stacks 080R "top row-partition block by an adjugate"]
theorem mul_toRows₁_adjugate (A : Matrix (ι ⊕ κ) ι R) :
    A * A.toRows₁.adjugate =
      fromRows (A.toRows₁.det • 1) (A.toRows₂ * A.toRows₁.adjugate) := sorry

end Matrix
