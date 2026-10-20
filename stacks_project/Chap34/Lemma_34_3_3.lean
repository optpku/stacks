/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.StandardZariskiCover.Refinement
import StacksCheckRecall

universe u v w

/- Lemma 34.3.3: every Zariski open cover of an affine scheme admits a finite standard Zariski
refinement whose members are open subschemes of selected members of the original cover. -/
@[stacks 020Q] #check
  (AlgebraicGeometry.Scheme.OpenCover.exists_standardRefinement :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]
      (𝒰 : T.OpenCover.{v}),
      ∃ (𝒱 : T.StandardZariskiCover.{u, w})
        (f : CategoryTheory.Precoverage.ZeroHypercover.Hom
          (AlgebraicGeometry.Scheme.precoverage @AlgebraicGeometry.IsOpenImmersion)
          𝒱.toOpenCover 𝒰),
        ∀ j : 𝒱.index, AlgebraicGeometry.IsOpenImmersion (f.h₀ j))
