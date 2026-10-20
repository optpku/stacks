/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.LocalAtSource
import StacksCheckRecall

universe u

/- Lemma 37.60.12: pseudo-coherence of scheme morphisms is syntomic local on the source. -/
@[stacks 0698] #check
  (AlgebraicGeometry.PseudoCoherent.isLocalAtSourceSyntomic :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.PseudoCoherent :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage)
