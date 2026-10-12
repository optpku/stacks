/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Etale

@[expose] public section

universe u

/- Lemma 34.4.4: an étale cover of an affine scheme admits a finite refinement by
affine schemes, each open affine in a member of the original cover. -/
@[stacks 0218] #check
  (AlgebraicGeometry.Scheme.Cover.exists_finite_affineRefinement :
    {T : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsAffine T] →
      (𝒰 : T.Cover AlgebraicGeometry.Scheme.etalePrecoverage) →
        ∃ (𝒱 : T.AffineCover (@AlgebraicGeometry.Etale)) (f : 𝒱.cover ⟶ 𝒰),
          Finite 𝒱.I₀ ∧ ∀ j, AlgebraicGeometry.IsOpenImmersion (f.h₀ j))
