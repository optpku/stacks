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

/- Definition 50.15.3: the complex `Ω^•_[X/S](log Y)` constructed in Lemma 50.15.2 is
the de Rham complex of log poles for the effective Cartier divisor `Y ⟶ X` over `S`. -/
@[stacks 0FUA] #check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.complex : ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) [IsEffectiveCartierDivisor i] (h_defined : AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined f i), CochainComplex (AlgebraicGeometry.RingedSpace.DeRham.Modules f.toLRSHom.toShHom) ℤ)
