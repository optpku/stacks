/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.Differentials

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.11.8: if `f : X ⟶ Y` is formally smooth, then its sheaf of relative
differentials `Ω[f.toShHom]` is locally projective on `X`. -/
@[stacks 06B5]
#check (AlgebraicGeometry.FormallySmooth.instIsLocallyProjectiveRelativeDifferentials :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.FormallySmooth f],
    AlgebraicGeometry.Scheme.Modules.IsLocallyProjective Ω[f.toShHom])
