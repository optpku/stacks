/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Generation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Coproduct
public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Derived pushforward between quasi-compact quasi-separated schemes has a right adjoint. -/
instance pushforwardIsLeftAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    (pushforwardCohomologyIn f).IsLeftAdjoint := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
