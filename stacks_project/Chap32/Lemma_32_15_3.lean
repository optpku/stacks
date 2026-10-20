/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.Proper
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 32.15.3: for a finite-type morphism `f : X ⟶ S` over a locally Noetherian scheme,
properness, the unrestricted valuative criterion, the DVR-valuative criterion, and the
generic-point DVR exists-unique criterion are equivalent. -/
@[stacks 0208] #check
  (AlgebraicGeometry.ValuativeCriterion.DVR.isProper_tfae :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f]
      [AlgebraicGeometry.IsLocallyNoetherian S],
      List.TFAE
        [ AlgebraicGeometry.IsProper f
        , AlgebraicGeometry.ValuativeCriterion f
        , AlgebraicGeometry.ValuativeCriterion.DVR f
        , AlgebraicGeometry.GenericPointDvrValuativeCriterionExistsUnique f
        ])
