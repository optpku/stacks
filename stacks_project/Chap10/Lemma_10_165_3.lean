/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.GeometricallyNormal.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Geometric normality and localization

Lemma 10.165.3, tag `06DE`, is owned by the reusable geometric-normality
localization API.

@stack 06DE
-/

/- Lemma 10.165.3, tag `06DE`: an arbitrary localization of a geometrically
normal field algebra is geometrically normal. -/
@[stacks 06DE]
#check @Algebra.IsGeometricallyNormal.of_isLocalization

/- Lemma 10.165.3, tag `06DE`: the canonical localization carries the
corresponding geometrically-normal instance. -/
@[stacks 06DE]
#check @Localization.instIsGeometricallyNormal
