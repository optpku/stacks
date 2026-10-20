/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Adjunction.Derived.Pointwise
import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.30.1

The triangulated-category statement is the direct specialization of the category-theoretic
pointwise derived-adjunction API.  Exactness and compatibility with triangulations govern the
domains of definition; the local Hom-set comparison itself only uses calculi of fractions and
essential constancy at the two chosen objects.
-/

/- Lemma 13.30.1 (Stacks 0FND) (1): pointwise left and right derived values of an adjoint pair
satisfy the canonical Hom-set equivalence. -/
@[stacks 0FND]
#check @CategoryTheory.Adjunction.Pointwise.homEquiv

/- Lemma 13.30.1 (Stacks 0FND) (2): the canonical Hom-set equivalence is functorial in the
left-derived variable wherever both values are defined. -/
@[stacks 0FND]
#check @CategoryTheory.Adjunction.Pointwise.HomEquiv.naturality_left

/- Lemma 13.30.1 (Stacks 0FND) (3): the canonical Hom-set equivalence is functorial in the
right-derived variable wherever both values are defined. -/
@[stacks 0FND]
#check @CategoryTheory.Adjunction.Pointwise.HomEquiv.naturality_right
