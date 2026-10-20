/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Components.Noetherian

/-!
# Normal locally Noetherian schemes and their components

This file characterizes normal locally Noetherian schemes by pairwise disjoint open covers by
normal integral open subschemes.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsLocallyNoetherian

/-- A locally Noetherian scheme is normal if and only if it admits a pairwise disjoint open cover
by normal integral open subschemes. -/
theorem isNormal_iff_hasPairwiseDisjointOpenCoverByNormalIntegral
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    X.isNormal ↔ X.HasPairwiseDisjointOpenCoverByNormalIntegral := sorry

end AlgebraicGeometry.IsLocallyNoetherian
