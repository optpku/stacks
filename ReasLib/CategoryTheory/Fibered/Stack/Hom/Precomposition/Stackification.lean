/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stackification and Hom precomposition

This leaf contains only the stackification-specific consequence for the generic
stack-to-ambient precomposition functor. Explicit quasi-inverse lift data live in
`StackOver.Hom.PrecompLift`.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

namespace StackOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- Precomposition from a bundled stack Hom category to the ambient Hom category is an
equivalence whenever `i` is a stackification. -/
@[stacks 04W9 "fixed-universe Hom property of stackification"]
theorem precomp_isEquivalence
    (Z : StackOver.{u, v, w, vS} J) {X : FiberedCategoryOver.{u, v, w, vS} C}
    {Y : StackOver.{u, v, w, vS} J} {i : X ⟶ Y.toFiberedCategoryOver}
    (hi : FiberedCategoryOver.Hom.IsStackification J i) :
    (precomp Z i).IsEquivalence := sorry

end StackOver.Hom

end CategoryTheory
