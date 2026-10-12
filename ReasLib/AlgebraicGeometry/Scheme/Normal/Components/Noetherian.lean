/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Components
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Normal Noetherian schemes and their components

This file characterizes normal schemes with Noetherian underlying spaces by finite pairwise
disjoint open covers by normal integral open subschemes.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme with Noetherian underlying space is normal if and only if it admits a finite
pairwise disjoint open cover by normal integral open subschemes. -/
theorem isNormal_iff_hasFinitePairwiseDisjointOpenCoverByNormalIntegral
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    X.isNormal ↔ X.HasFinitePairwiseDisjointOpenCoverByNormalIntegral := sorry

end AlgebraicGeometry.Scheme
