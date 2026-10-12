/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Preadditive
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.11

The normalized finite-filtered homotopy object is owned by
`ReasLib.CategoryTheory.Filtration.Derived.Preadditive`.  Its locality and both Hom-bijection
views are exposed there without source-local additive instances or transports.
-/

namespace CategoryTheory.FilteredObject.FiniteDerived.Locality

/- Lemma 13.26.11 (1) (`05TY`): precomposition with a filtered quasi-isomorphism is bijective
on maps into a bounded-below complex of filtered injectives. -/
@[stacks 05TY "(1)"] #check @precompBijective

/- Lemma 13.26.11 (2) (`05TY`): the finite filtered derived quotient is bijective on maps into
a bounded-below complex of filtered injectives. -/
@[stacks 05TY "(2)"] #check @mapBijective

end CategoryTheory.FilteredObject.FiniteDerived.Locality
