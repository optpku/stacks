/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
import StacksCheckRecall

/-!
@stack 0179

# Lemma 14.11.5 compatibility facade

Mathlib directly owns the additive dimension bound for cartesian products of simplicial sets.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

universe u

variable (U V : SSet.{u}) (a b : ℕ) [U.HasDimensionLE a] [V.HasDimensionLE b]

/- Lemma 14.11.5: `dim (U × V) ≤ a + b` when `dim U ≤ a` and `dim V ≤ b`. -/
@[stacks 0179]
#check (inferInstance : (U ⊗ V).HasDimensionLE (a + b))

#check SSet.hasDimensionLE_prod
