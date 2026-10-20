/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over.OpenNeighborhood

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 70.18.3: For a scheme `S`, a retrocompact open `U`, and a point `s`
outside `U`, restriction induces an equivalence from the colimit over open
neighborhoods containing `U` and `s` to finite-presentation algebraic spaces
over `U` and the local spectrum, glued over their intersection. -/
@[stacks 0E91] #check
  (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.comparison_isEquivalence :
    ∀ (S : Scheme.{u}) (U : S.Opens) [AlgebraicGeometry.QuasiCompact U.ι] (s : S),
      s ∉ (U : Set S) →
        (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.OpenNeighborhood.comparison
          S U s).IsEquivalence)
