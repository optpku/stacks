/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Lemma 35.23.32 (1): the property that a scheme morphism is finite locally free is
fpqc local on the base. -/
@[stacks 02VO] #check
  (AlgebraicGeometry.IsFiniteLocallyFree.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsFiniteLocallyFree :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)

/- Lemma 35.23.32 (2): for fixed `d : ℕ`, the property that a scheme morphism is
finite locally free of degree `d` is fpqc local on the base. -/
@[stacks 02VO] #check
  (AlgebraicGeometry.IsFiniteLocallyFreeOfRank.isLocalAtTargetFpqc :
    ∀ d : ℕ,
      MorphismProperty.IsLocalAtTarget
        ((fun _ _ f ↦ AlgebraicGeometry.IsFiniteLocallyFreeOfRank f d) :
          MorphismProperty AlgebraicGeometry.Scheme.{u})
        AlgebraicGeometry.Scheme.fpqcPrecoverage)
