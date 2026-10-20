/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.Factorization

open CategoryTheory

universe u

/- Remark 29.42.3: the uniqueness assumption on the dotted arrows in Lemma 29.42.2 is necessary
(details omitted). If `f` is separated, uniqueness is guaranteed by Schemes, Lemma 26.22.1. -/
@[stacks 0895] #check
  (AlgebraicGeometry.ValuativeCriterion.Along.uniqueness_of_isSeparated :
    ∀ {U X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
      [AlgebraicGeometry.IsSeparated f],
      AlgebraicGeometry.ValuativeCriterion.Along.Uniqueness h f)
