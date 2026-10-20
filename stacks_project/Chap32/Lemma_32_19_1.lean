/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.TopDegreeBaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 32.19.1: for a morphism between quasi-compact and quasi-separated schemes, vanishing
of quasicoherent higher direct images above `d` implies that arbitrary base change preserves the
vanishing bound and satisfies the degree-`d` projection formula and further-base-change
compatibility. -/
@[stacks 0EX3] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.topDegreeBaseChange_of_vanishesAbove :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
      [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
      [CompactSpace Y.carrier] [QuasiSeparatedSpace Y.carrier],
      AlgebraicGeometry.Scheme.HigherDirectImage.VanishesAbove f d →
        AlgebraicGeometry.Scheme.HigherDirectImage.TopDegreeBaseChange f d)
