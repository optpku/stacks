/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Composition
import StacksCheckRecall

@[expose] public section

/- The canonical Mathlib/ReasLib owners for composition on bounded-below homotopy and derived
categories. -/

#check @CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso
#check @CategoryTheory.Functor.toBoundedBelowDerived.compIsoOfIso
#check @CategoryTheory.Functor.toBoundedBelowDerived.compIso
