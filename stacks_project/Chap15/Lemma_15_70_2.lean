/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude.Ext
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.70.2: injective amplitude from Ext vanishing

The reusable theorem is split between the generic derived-category criterion and the
module-specific ideal-quotient criterion.  This source file records the exact three-clause Stacks
statement without retaining chapter-local resolution or truncation infrastructure.

@stack 0A5T
-/

/- Lemma 15.70.2, tag `0A5T`: injective amplitude in `[a, b]`, vanishing of derived Ext from all
modules outside `[a, b]`, and vanishing from all ideal quotients are equivalent. -/
@[stacks 0A5T]
#check @CategoryTheory.DerivedCategory.InjectiveAmplitude.ext_tfae

/- Generic forward vanishing requires no enough-injectives assumption. -/
#check @CategoryTheory.DerivedCategory.HasInjectiveAmplitudeIn.ext_subsingleton

/- The fine-grained reconstruction criterion only assumes explicit t-structure bounds and enough
injectives. -/
#check @CategoryTheory.DerivedCategory.InjectiveAmplitude.iff_isGE_isLE_ext_succ

/- The all-heart-object criterion is reusable in any abelian category with enough projectives and
injectives. -/
#check @CategoryTheory.DerivedCategory.InjectiveAmplitude.iff_ext_subsingleton

/- Ideal quotients are a module-specific test family. -/
#check @CategoryTheory.DerivedCategory.InjectiveAmplitude.iff_idealQuotient_ext_subsingleton
