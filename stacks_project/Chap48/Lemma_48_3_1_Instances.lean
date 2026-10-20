/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import stacks_project.Chap36.Lemma_36_4_1

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Compatibility: the shared instance applies to the source-facing derived pushforward
abbreviation. -/
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardIsLeftAdjoint :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      [CompactSpace X] → [QuasiSeparatedSpace X] →
      [CompactSpace Y] → [QuasiSeparatedSpace Y] →
      (AlgebraicGeometry.Scheme.DerivedQCoh.pushforward f).IsLeftAdjoint)
