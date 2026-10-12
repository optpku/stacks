/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Refinement
import StacksCheckRecall

universe u v

/- Lemma 34.9.12: a pointwise flat family of scheme morphisms is fpqc-covering
if every affine base change admits a standard fpqc cover refining the pulled-back
family. -/
@[stacks 03LB] #check
  (AlgebraicGeometry.Scheme.fpqcCovering_of_flat_of_affine_pullback_standard_refinement :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → CategoryTheory.Over T),
      (∀ i : ι, AlgebraicGeometry.Flat (X i).hom) →
        (∀ ⦃Z : AlgebraicGeometry.Scheme.{u}⦄,
          AlgebraicGeometry.IsAffine Z →
            ∀ h : Z ⟶ T,
              ∃ 𝒰 : AlgebraicGeometry.StandardFpqcCover Z,
                CategoryTheory.SemiRepresentableFamily.Over.Refines
                  𝒰.toOverFamily
                  (CategoryTheory.SemiRepresentableFamily.Over.ofArrows
                    (fun i ↦ CategoryTheory.Limits.pullback h (X i).hom)
                    (fun i ↦ CategoryTheory.Limits.pullback.fst h (X i).hom))) →
          AlgebraicGeometry.Scheme.FpqcCovering X)
