/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped CategoryTheory

/- Definition 13.11.3 (`05RU`): the derived category and its bounded-below, bounded-above, and
bounded full subcategories use the canonical Mathlib/ReasLib owners. -/
@[stacks 05RU] #check DerivedCategory
@[stacks 05RU] #check DerivedCategory.homologyFunctor
@[stacks 05RU] #check DerivedCategory.Plus
@[stacks 05RU] #check DerivedCategory.Minus
@[stacks 05RU] #check DerivedCategory.Bounded
@[stacks 05RU] #check DerivedCategory.Plus.ι
@[stacks 05RU] #check DerivedCategory.Minus.ι
@[stacks 05RU] #check DerivedCategory.Bounded.ι
@[stacks 05RU] #check CategoryTheory.DerivedCategory.Minus.homologyFunctor
@[stacks 05RU] #check CategoryTheory.DerivedCategory.Bounded.homologyFunctor
@[stacks 05RU] #check CategoryTheory.DerivedCategory.plus_iff
@[stacks 05RU] #check CategoryTheory.DerivedCategory.minus_iff
@[stacks 05RU] #check CategoryTheory.DerivedCategory.bounded_iff
