/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.TruncationSplitting
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.27.9

The Ext-vanishing splitting construction is owned by the neutral derived-category API.  This
source file only records the Stacks-facing recall: the intrinsic shifted cohomology family is
defined for every derived object, while interval bounds belong to the finite-biproduct
realization.
-/

/- Lemma 13.27.9 (1): `i ↦ H^i(K)[-i]` is the intrinsic shifted cohomology family. -/
@[stacks 0GM4] #check @DerivedCategory.ShiftedCohomology.family

/- Lemma 13.27.9 (2): the finite interval restriction realizes the shifted cohomology family
over a chosen cohomological amplitude. -/
@[stacks 0GM4] #check @DerivedCategory.ShiftedCohomology.on

/- Lemma 13.27.9 (3): higher-Ext vanishing splits each bounded-below upper truncation into the
corresponding finite biproduct. -/
@[stacks 0GM4] #check @DerivedCategory.ShiftedCohomology.Split.truncLE

/- Lemma 13.27.9 (4): the bounded-amplitude form splits a derived object over any prescribed
cohomological support interval. -/
@[stacks 0GM4] #check @DerivedCategory.ShiftedCohomology.Split.ofBounds

/- Lemma 13.27.9 (5): a bounded derived object has some finite shifted-cohomology biproduct
decomposition under the same Ext-vanishing condition. -/
@[stacks 0GM4] #check @DerivedCategory.ShiftedCohomology.Split.bounded
