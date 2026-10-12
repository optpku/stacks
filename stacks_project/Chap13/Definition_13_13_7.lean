/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Bounded.Relations
import StacksCheckRecall

@[expose] public section

/- Definition 13.13.7 (`05S4`): bounded finite-filtered derived categories are full subcategories
cut out by the standard t-structure after derived associated graded. -/
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Plus.property
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Minus.property
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Bounded.property
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Plus.Category
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Minus.Category
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Bounded.Category

/- Membership, the two-sided intersection, and canonical inclusions are the reusable API around
the three category owners. -/
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Plus.mem_iff
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Minus.mem_iff
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Bounded.mem_iff
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Bounded.property_eq_inf
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Plus.inclusion
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Minus.inclusion
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Bounded.inclusion
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Bounded.ToPlus.inclusion
@[stacks 05S4] #check @CategoryTheory.FilteredObject.FiniteDerived.Bounded.ToMinus.inclusion
