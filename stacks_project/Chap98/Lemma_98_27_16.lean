/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.OpennessOfVersality
import StacksCheckRecall

/-! # Openness of versality for the Artin contraction functor -/

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 98.27.16: In Situation 98.27.1 the contraction functor satisfies
openness of versality. -/
@[stacks 0GIA] #check (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.opennessOfVersality :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (σ : AlgebraicGeometry.AlgebraicSpace.ContractionSituation S),
    AlgebraicGeometry.Scheme.Over.OpennessOfVersality σ.functor)
