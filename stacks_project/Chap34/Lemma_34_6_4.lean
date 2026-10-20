/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Syntomic.StandardRefinement
import StacksCheckRecall

universe u v

/- Lemma 34.6.4: every syntomic covering of an affine scheme admits a finite
refinement by standard syntomic affine charts that are open affine subschemes
of members of the original covering. -/
@[stacks 0228] #check
  (AlgebraicGeometry.SyntomicCover.exists_standardRefinement :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]
      (𝒰 : AlgebraicGeometry.SyntomicCover.{u, v} T),
      ∃ 𝒱 : AlgebraicGeometry.StandardSyntomicCovering T,
        ∃ φ : CategoryTheory.Precoverage.ZeroHypercover.Hom
            (AlgebraicGeometry.Scheme.precoverage (@AlgebraicGeometry.Syntomic))
            𝒱.toSyntomicCover 𝒰,
          ∀ j : Fin 𝒱.n, AlgebraicGeometry.IsOpenImmersion (φ.h₀ j))
