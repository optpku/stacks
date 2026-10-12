/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Limit.BoundedBelow
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.34.3

The bounded-below derived-limit existence theorem is owned by the neutral
`DerivedCategory.Plus` API.  The source item is a direct tagged recall, so
its injective-model and Milnor-triangle implementation is not duplicated in
Chapter 13.
-/

/- Lemma 13.34.3 (Stacks 0BK7): a sequential inverse system in `D⁺(𝒜)` has a
derived inverse limit in `D(𝒜)` when `𝒜` has countable products and enough
injectives. -/
@[stacks 0BK7] #check @CategoryTheory.DerivedCategory.Plus.exists_derivedLimit
