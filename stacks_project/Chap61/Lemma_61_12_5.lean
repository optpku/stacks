/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.Refinement
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.12.5: a pro-étale cover of an affine scheme admits a finite refinement by
affine schemes, each open affine in a member of the original cover. -/
@[stacks 098D] #check
  (AlgebraicGeometry.Scheme.Proetale.exists_finite_affineRefinement :
    {T : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsAffine T] →
      (𝒰 : T.Cover AlgebraicGeometry.Scheme.proetalePrecoverage) →
        ∃ (𝒱 : T.AffineCover (@AlgebraicGeometry.WeaklyEtale))
          (f : 𝒱.cover ⟶ 𝒰.forgetQc),
          Finite 𝒱.I₀ ∧ ∀ j, AlgebraicGeometry.IsOpenImmersion (f.h₀ j))
