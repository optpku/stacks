/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap48.Lemma_48_3_1_Instances
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.3.1: for a morphism `f : X ⟶ Y` between quasi-compact quasi-separated
schemes, derived pushforward on `DerivedQCoh` has a right adjoint. -/
@[stacks 0A9E] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardIsLeftAdjoint :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      [CompactSpace X] → [QuasiSeparatedSpace X] →
      [CompactSpace Y] → [QuasiSeparatedSpace Y] →
      (AlgebraicGeometry.Scheme.DerivedQCoh.pushforward f).IsLeftAdjoint)
