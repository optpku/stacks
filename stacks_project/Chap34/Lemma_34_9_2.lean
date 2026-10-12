/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Criteria
import StacksCheckRecall

universe u v

/- Lemma 34.9.2: an indexed family of scheme morphisms is an fpqc covering if
and only if it satisfies the affine local image-cover criterion. -/
@[stacks 03L7] #check
  (AlgebraicGeometry.Scheme.Fpqc.Criterion.cover_iff_affine :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → CategoryTheory.Over T),
      AlgebraicGeometry.Scheme.FpqcCovering X ↔
        AlgebraicGeometry.Scheme.Fpqc.Criterion.Affine X)

#check
  (AlgebraicGeometry.Scheme.Fpqc.Criterion.affine_iff_refinement :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → CategoryTheory.Over T),
      AlgebraicGeometry.Scheme.Fpqc.Criterion.Affine X ↔
        AlgebraicGeometry.Scheme.Fpqc.Criterion.Refinement X)

#check
  (AlgebraicGeometry.Scheme.Fpqc.Criterion.affine_iff_neighborhood :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → CategoryTheory.Over T) [QuasiSeparatedSpace T],
      AlgebraicGeometry.Scheme.Fpqc.Criterion.Affine X ↔
        AlgebraicGeometry.Scheme.Fpqc.Criterion.Neighborhood X)
