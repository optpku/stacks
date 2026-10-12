/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Complex Composable Rows

This leaf owns elementary operations on the canonical `ComposableArrows.IsComplex`
predicate. It is independent of pretriangulated categories and can be imported by
any development that needs to extend a complex row on the left.
-/

open scoped ZeroObject

universe v u

namespace CategoryTheory

namespace ComposableArrows

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroMorphisms D]

/-- Restricting a complex row to any consecutive finite subrow preserves complexness. -/
@[stacks 0D81]
theorem natAddLEFunctor_obj_isComplex {n k l : ℕ} (h : k + l ≤ n)
    {R : ComposableArrows D n} (hR : R.IsComplex) :
    ((natAddLEFunctor h).obj R).IsComplex := sorry

namespace IsComplex

/-- Dropping the first arrow of a complex row preserves complexness. -/
@[stacks 0D81]
theorem δ₀ {n : ℕ} {R : ComposableArrows D (n + 1)} (hR : R.IsComplex) :
    R.δ₀.IsComplex := sorry

/-- Dropping the last arrow of a complex row preserves complexness. -/
@[stacks 0D81]
theorem δlast {n : ℕ} {R : ComposableArrows D (n + 1)} (hR : R.IsComplex) :
    R.δlast.IsComplex := sorry

end IsComplex

/-- Prepending an arrow whose new adjacent composite vanishes preserves complexness. -/
@[stacks 0D81]
theorem isComplex_precomp {n : ℕ} {R : ComposableArrows D (n + 1)} {X : D}
    {f : X ⟶ R.left} (hR : R.IsComplex) (hf : f ≫ R.map' 0 1 = 0) :
    (R.precomp f).IsComplex := sorry

end

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroMorphisms D] [Limits.HasZeroObject D]

/-- Prepending the zero morphism to a complex row preserves complexness. -/
@[stacks 0D81]
theorem isComplex_precomp_zero {n : ℕ} (R : ComposableArrows D n) (hR : R.IsComplex) :
    (R.precomp (0 : (0 : D) ⟶ R.left)).IsComplex := sorry

end

end ComposableArrows

end CategoryTheory
