/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.RimSchlessinger
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.TangentSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 98.27.12: In the standing contraction situation, the functor of
compatible triples satisfies the Rim-Schlessinger condition. -/
@[stacks 0GI6] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.hasRimSchlessinger :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
      (σ : AlgebraicGeometry.AlgebraicSpace.ContractionSituation S),
      AlgebraicGeometry.Scheme.Over.HasRimSchlessinger σ.functor)
