/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Polarized.Algebraic
import StacksCheckRecall

open CategoryTheory.Limits

universe u

/- Lemma 99.14.6: The forgetful morphism from polarized proper schemes to
finite-presentation flat proper algebraic-space families is algebraic. -/
@[stacks 0D41] #check (AlgebraicGeometry.Polarized.instAlgebraicStack_twoFibreProduct :
  ∀ ξ : AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
      (⊤_ AlgebraicGeometry.Scheme.{u}),
    AlgebraicGeometry.AlgebraicStack (AlgebraicGeometry.Polarized.twoFibreProduct ξ))
