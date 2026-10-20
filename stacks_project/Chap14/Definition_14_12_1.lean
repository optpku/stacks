module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import StacksCheckRecall

/-!
@stack 0180
-/

@[expose] public section

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] (n : ℕ)

/- Definition 14.12.1: `n`-truncated simplicial objects are functors on the opposite truncated
simplex category. -/
@[stacks 0180]
#check (SimplicialObject.Truncated C n)

#check (SSet.Truncated.{u} n)
