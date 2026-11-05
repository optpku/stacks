/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective.RightDerived

/-!
# Equation 13.26.13.6

The equation `RT = T_ext ∘ j'` is represented categorically by the canonical natural
isomorphism between a right-derived functor and its computation through the bounded-below
filtered-injective model.  ReasLib owns both that comparison and the equivalence certificate
available under enough injectives.
-/

/- Equation 13.26.13.6 (`05U2`): the equation `RT = T_ext ∘ j'` is the canonical comparison between
a bounded-below finite filtered right-derived functor and the composite obtained by first taking
the inverse filtered-injective representative and then applying `T_ext`. -/
@[stacks 05U2] #check @isoOfEnoughInjectives

/- The certificate-taking comparison remains available when working with a transported
filtered-injective equivalence. -/
#check @iso

/- Under enough injectives, the filtered-injective model equivalence required by the preceding
comparison is supplied canonically. -/
#check @CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective.isEquivalence

/- The comparison is characterized by its compatibility with the two right-derived
factorizations, both globally and componentwise. -/
#check @isoOfEnoughInjectives.fac
#check @isoOfEnoughInjectives.fac_app
#check @isoOfEnoughInjectives.inv_fac
#check @isoOfEnoughInjectives.inv_fac_app
