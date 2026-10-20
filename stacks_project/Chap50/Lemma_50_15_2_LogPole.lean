/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole.ResidueSequence

@[expose] public section

open CategoryTheory ComplexShape
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.LogPole

/-- The canonical logarithmic residue sequence is short exact. -/
abbrev logPoleSequence_shortExact {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i]
    (h_defined : AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined f i) :
    (AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.canonicalSequence
      h_defined).ShortExact :=
  AlgebraicGeometry.RingedSpace.DeRham.LogPole.Canonical.canonicalSequence_shortExact
    f i h_defined

end AlgebraicGeometry.Scheme.DeRham.LogPole
