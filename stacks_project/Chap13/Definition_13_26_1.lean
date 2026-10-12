/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.FiniteInjective
import StacksCheckRecall

@[expose] public section

/- Domain-style sampling for Definition 13.26.1:
- primary domain: filtered objects in an abelian category, specialized to the full subcategory of
  finite filtered objects;
- sampled owner declarations:
  `Injective`,
  `CochainComplex.IsKInjective`,
  `FilteredObject.IsFilteredInjective`,
  `FilteredObject.Finite.FilteredInjective.property`,
  `gr^{p}`,
  `FilteredObject.Finite.category`;
- owner abstraction: the graded-piece condition is the general class
  `FilteredObject.IsFilteredInjective`; its finite-object specialization is the property
  `FilteredObject.Finite.FilteredInjective.property`, not a root-level wrapper;
- source/core/bridge triage:
  `source-facing`: filtered injective objects of `Fil^f(𝒜)`;
  `core/canonical`: the general class and its finite-object property;
  `bridge/view`: the graded-piece characterization built into that owner.

This item is therefore a pure canonical-recall entry: the textbook definition already matches the
existing chapter owner exactly, so the file should recall that owner directly rather than
reintroducing a duplicate alias or `_iff` wrapper. -/

/- Definition 13.26.1: for an abelian category `𝒜`, an object `I` of `Fil^f(𝒜)` is filtered
injective when each graded piece `gr^p(I)` is an injective object of `𝒜`. The chapter owner is
the general class `FilteredObject.IsFilteredInjective`, specialized to finite filtered objects by
`FilteredObject.Finite.FilteredInjective.property`. -/
#check @CategoryTheory.FilteredObject.IsFilteredInjective
@[stacks 015P] #check @CategoryTheory.FilteredObject.Finite.FilteredInjective.property
