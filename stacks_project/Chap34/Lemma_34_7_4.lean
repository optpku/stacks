/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.Refinement

@[expose] public section

universe u

/- Lemma 34.7.4: an fppf cover of an affine scheme admits a finite refinement by
affine schemes, each open affine in a member of the original cover. -/
@[stacks 021P] #check
  (AlgebraicGeometry.Scheme.Fppf.exists_finite_affineRefinement :
    {T : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsAffine T] →
      (𝒰 : T.Cover AlgebraicGeometry.Scheme.fppfPrecoverage) →
        ∃ (𝒱 : T.AffineCover
            ((@AlgebraicGeometry.Flat) ⊓
              (@AlgebraicGeometry.LocallyOfFinitePresentation :
                CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme)))
            (f : 𝒱.cover ⟶ 𝒰),
          Finite 𝒱.I₀ ∧ ∀ j, AlgebraicGeometry.IsOpenImmersion (f.h₀ j))
