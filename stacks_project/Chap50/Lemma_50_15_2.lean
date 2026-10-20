/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole.ResidueSequence

@[expose] public section

open CategoryTheory ComplexShape
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 50.15.2: for an effective Cartier divisor `Y` in `X`, a defined logarithmic
de Rham complex has a canonical short exact residue sequence
`0 ⟶ Ωᐧ_[X/S] ⟶ Ωᐧ_[X/S](log Y) ⟶ Ωᐧ_[Y/S][-1] ⟶ 0`. -/
@[stacks 0FMW] #check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.canonicalSequence_shortExact : ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (h_defined : AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined f i), (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.canonicalSequence h_defined).ShortExact)
