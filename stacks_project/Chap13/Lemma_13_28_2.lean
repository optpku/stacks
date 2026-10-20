/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Bounded.K0
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.28.2

The canonical identification between the Grothendieck group of an abelian
category and the triangulated Grothendieck group of its bounded derived
category is owned by `DerivedCategory.Bounded.K0`.
-/

open CategoryTheory

/- Lemma 13.28.2: degree-zero objects induce the canonical equivalence
`AbelianK0 A ≃+ TriangulatedK0 (DerivedCategory.Bounded A)`. -/
@[stacks 0FCP] #check @DerivedCategory.Bounded.K0.equiv

/- Companion check: the forward map is induced by the degree-zero embedding. -/
@[stacks 0FCP] #check @DerivedCategory.Bounded.K0.fromAbelian

/- Companion check: the inverse map is the cohomological Euler characteristic. -/
@[stacks 0FCP] #check @DerivedCategory.Bounded.K0.toAbelian

/- Companion check: the equivalence computes on degree-zero object classes. -/
@[stacks 0FCP] #check @DerivedCategory.Bounded.K0.equiv_apply_of

/- Companion check: its inverse computes on bounded-derived object classes. -/
@[stacks 0FCP] #check @DerivedCategory.Bounded.K0.equiv_symm_apply_of
