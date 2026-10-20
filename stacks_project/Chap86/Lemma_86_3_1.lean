/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 86.3.1: for a morphism `f : X ⟶ Y` of quasi-compact quasi-separated
algebraic spaces over a scheme `S`, derived pushforward on `DerivedQCoh` has a
right adjoint. -/
@[stacks 0E55] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardIsLeftAdjoint :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsQuasiCompact X] → [IsAbsolutelyQuasiSeparated X] →
      [IsQuasiCompact Y] → [IsAbsolutelyQuasiSeparated Y] →
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn f).IsLeftAdjoint)
