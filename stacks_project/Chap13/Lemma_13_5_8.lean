/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.ObjectProperty.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Localization of a Full Triangulated Subcategory

This source entry is a thin textbook bridge.  The reusable constructions and criteria live in
`ReasLib.CategoryTheory.ObjectProperty.Localization`.
-/

namespace CategoryTheory

/- Lemma 13.5.8: a saturated multiplicative system restricted to a full triangulated
subcategory has the canonical localization comparison.  A denominator cover gives an
equivalence, while the triangulated restriction API supplies compatibility with shifts and
distinguished triangles. -/
@[stacks 0GSL] #check @fullSubcategoryLocalizerMorphism.cover.isLocalizedEquivalence

/- The two independent localization criteria and the triangulated restriction API are available
without importing this chapter file. -/
@[stacks 0GSL] #check @fullSubcategoryLocalizerMorphism.invariance.isLocalizedFullyFaithful

@[stacks 0GSL] #check @fullSubcategoryLocalizerMorphism.hasLeftResolutions_iff

@[stacks 0GSL] #check @fullSubcategoryLocalizationSystem.complete₃

/- The comparison isomorphism is reusable as structured shift-compatible naturality data, and
the induced functor has direct component formulas on objects coming from the source localization. -/
@[stacks 0GSL] #check @fullSubcategoryLocalizationFunctor.facIso

@[stacks 0GSL] #check @fullSubcategoryLocalizationFunctor.facIso.hom_naturality

@[stacks 0GSL] #check @fullSubcategoryLocalizationFunctor.facIso.inv_naturality

@[stacks 0GSL] #check @fullSubcategoryLocalizationFunctor.map_Q

@[stacks 0GSL] #check @LocalizerMorphism.facIso.homCommShift

@[stacks 0GSL] #check @LocalizerMorphism.localizedFunctor.commShiftIso_hom_app

@[stacks 0GSL] #check @LocalizerMorphism.localizedFunctor.commShiftIso_inv_app

end CategoryTheory
