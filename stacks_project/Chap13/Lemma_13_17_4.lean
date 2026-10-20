/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Serre
import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison.Minus
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.17.4

The bounded-above comparison for a Serre subcategory is owned by
`DerivedCategory.Minus.CohomologyIn.Comparison`.  Its source hypothesis is
the reusable class `ObjectProperty.HasEpiLift`.
-/

open CategoryTheory

/- Lemma 13.17.4: under the epi-lift hypothesis, the canonical comparison
`D⁻(P) ⟶ D⁻_P(A)` is an equivalence. -/
@[stacks 0FCL]
#check @DerivedCategory.Minus.CohomologyIn.Comparison.isEquivalence

/- Companion check: the epi-lift hypothesis has a shared object-property owner. -/
@[stacks 0FCL] #check @ObjectProperty.HasEpiLift

/- Companion check: the bounded-above comparison functor is concrete and reusable. -/
@[stacks 0FCL] #check @DerivedCategory.Minus.CohomologyIn.Comparison.functor

/- Companion computations: both lift layers expose their underlying object
and morphism maps without unfolding full-subcategory constructions. -/
@[stacks 0FCL]
#check @DerivedCategory.Minus.CohomologyIn.Comparison.Ambient.functor.obj_obj

@[stacks 0FCL]
#check @DerivedCategory.Minus.CohomologyIn.Comparison.Ambient.functor.map_hom

@[stacks 0FCL]
#check @DerivedCategory.Minus.CohomologyIn.Comparison.functor.obj_obj

@[stacks 0FCL]
#check @DerivedCategory.Minus.CohomologyIn.Comparison.functor.map_hom

/- Companion check: the seeded complex replacement is available independently. -/
@[stacks 0FCL]
#check @CochainComplex.Minus.TermsIn.exists_seeded_mono_of_homology
