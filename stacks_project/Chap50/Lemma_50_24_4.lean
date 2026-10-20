/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.TopDifferential
public import stacks_project.Chap50.Situation_50_24_1
public import stacks_project.Chap50.Lemma_50_3_5_DerivedDeRham

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Lemma 50.24.4: in Situation 50.24.1, the map on degree-`n` higher direct images
induced by `d : Ω^(n - 1)_{X/S} ⟶ Ω^n_{X/S}` is zero. -/
@[stacks 0G8J] #check
  (AlgebraicGeometry.Scheme.DeRham.topHigherDirectImageDifferential_eq_zero :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
      [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
      [AlgebraicGeometry.Scheme.Hom.RelativeDimension f n],
      (∀ s : S, Nonempty (f.fiber s)) →
        AlgebraicGeometry.Scheme.DeRham.topHigherDirectImageDifferential f n = 0)
