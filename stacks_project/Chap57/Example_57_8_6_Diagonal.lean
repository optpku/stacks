/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDiagonal

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/- The relative diagonal kernel is provided by the shared derived quasicoherent module API. -/
#check (AlgebraicGeometry.Scheme.FourierMukai.relativeDiagonalKernel :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S),
    RingedSpace.ModuleDerived (Limits.pullback f f).toRingedSpace)

end AlgebraicGeometry.Scheme.FourierMukai
