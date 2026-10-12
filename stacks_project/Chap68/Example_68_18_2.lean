/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import stacks_project.Chap68.Example_68_18_2_Fibre
public import stacks_project.Chap68.Example_68_18_2_Presentation
public import stacks_project.Chap68.Example_68_18_2_Space

/-!
# An infinite fibre of points of algebraic spaces
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre
open AlgebraicGeometry.AlgebraicSpace.Points

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre

/-- Example 68.18.2 (1): for a characteristic-zero field `K` with an automorphism `σ` of
infinite order, the square `𝔸¹_K ⟶ Spec(K)` over `𝔸¹_K/ℤ ⟶ Spec(K)/ℤ` of algebraic spaces
over `Spec(ULift ℤ)` is cartesian. -/
@[stacks 0AC4]
theorem isPullback (K : Type u) [Field K] [CharZero K] (σ : RingAut K)
    (hσ : ¬ IsOfFinOrder σ) :
    IsPullback (q K) (p K σ) (g K σ hσ) (f K σ hσ) := sorry

/-- Example 68.18.2 (2): with `x` the image of `t = 0` in `𝔸¹_K/ℤ` and `z` the unique point
of `Spec(K)`, the fibre `F_{x, z}` equals the set of integer points of `𝔸¹_K`, hence is `ℤ`
as a set. -/
@[stacks 0AC4]
theorem fibre_eq_range_integerPoint (K : Type u) [Field K] [CharZero K] (σ : RingAut K)
    (hσ : ¬ IsOfFinOrder σ) :
    fibre (p K σ) (q K) (x K σ) (z K) = Set.range (integerPoint K) := sorry

end AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre
