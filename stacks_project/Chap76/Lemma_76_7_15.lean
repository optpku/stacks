/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.FinitePresentation
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 76.7.15: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. If `f` is locally of finite presentation, then `Ω[f]` is a finitely presented
`𝒪_X`-module. -/
@[stacks 05ZF]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeDifferentials.isFinitePresentation :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f],
      (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDifferentials f).IsFinitePresentation)
