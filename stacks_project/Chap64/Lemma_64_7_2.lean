/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Injective
import stacks_project.Chap64.Lemma_64_7_2_Projective
import stacks_project.Chap64.Lemma_64_7_2_Minus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 64.7.2 (1): if C has enough injectives, then DF⁺(C) ≌ K⁺(I), where I is the
full additive subcategory of Filᶠ(C) consisting of filtered injective objects. -/
@[stacks 03TB] #check @FilteredObject.FiniteDerived.Plus.FilteredInjective.equivalenceOfEnoughInjectives

/- Lemma 64.7.2 (2): if C has enough projectives, then DF⁻(C) ≌ K⁻(P), where P is the
full additive subcategory of Filᶠ(C) consisting of filtered projective objects. -/
@[stacks 03TB] #check @FilteredObject.FiniteDerived.Minus.FilteredProjective.equivalenceOfEnoughProjectives
