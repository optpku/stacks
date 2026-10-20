/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorDimension.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total

/-! # Tor-independent base change of relative Tor-amplitude

Derived pullback preserves relative Tor-amplitude under Tor-independent base change,
and ordinary pullback computes it on modules flat over the base.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- In a Tor-independent cartesian square of algebraic spaces, derived pullback
preserves a fixed Tor-amplitude interval relative to the base. -/
theorem hasTorAmplitudeInOver
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (E : ModuleDerived X) (a b : ℤ)
    (hE : ModuleDerived.HasTorAmplitudeInOver f E a b) :
    ModuleDerived.HasTorAmplitudeInOver f' ((ModuleDerived.pullback g').obj E) a b :=
  sorry

/-- In a Tor-independent cartesian square of algebraic spaces, a module flat over
the base computes derived pullback at its degree-zero complex. -/
theorem computesAtSingle
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (M : Modules X) (hM : Modules.IsFlatOver M f) :
    Functor.LeftDerived.ComputesAt (Functor.Homotopy.toDerived (Modules.pullback g'))
      (HomotopyCategory.quasiIso (Modules X) (up ℤ))
      ((HomotopyCategory.singleFunctor (Modules X) 0).obj M) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange
