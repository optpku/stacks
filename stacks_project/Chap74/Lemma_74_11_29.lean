/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Fpqc
public import stacks_project.Chap74.Lemma_74_11_29_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.29: the property `P(f)` given by “`f` is finite locally free” is
fpqc local on the base. -/
@[stacks 042C] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.FiniteLocallyFree S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
