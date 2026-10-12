/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_25_4_Normal
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Normal integral affine étale charts

A point of a normal integral algebraic space is in the image of an étale morphism
from a normal integral affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.4.5: Let `S` be a scheme. Let `X` be a normal integral algebraic
space over `S`. For every `x ∈ Points X` there exists a normal integral affine
scheme `U` and an étale morphism `U ⟶ X` such that `x` is in the image. -/
@[stacks 0AYH]
theorem exists_isAffine_isNormal_isIntegral_etale {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsNormal X] [IsIntegral X] (x : Points X) :
    ∃ (U : Over S) (f : ofOver U ⟶ X) (u : U.left),
      AlgebraicGeometry.IsAffine U.left ∧ Scheme.isNormal U.left ∧
        AlgebraicGeometry.IsIntegral U.left ∧ Etale f ∧
          Points.mapOfOver f u = x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
