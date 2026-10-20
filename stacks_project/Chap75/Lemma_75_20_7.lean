/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorDimension.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ChartRestriction
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace ComplexShape

universe u

/- Lemma 75.20.7 (1): in a Tor-independent cartesian square of algebraic spaces,
derived pullback preserves a fixed Tor-amplitude interval relative to the base. -/
@[stacks 0DKD] #check
  (AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.hasTorAmplitudeInOver :
    {S : Scheme.{u}} → {X' X Y' Y : AlgebraicSpace S} →
      (g' : X' ⟶ X) → (f' : X' ⟶ Y') → (f : X ⟶ Y) → (g : Y' ⟶ Y) →
      (sq : IsPullback g' f' f g) →
      (hTor : TorIndependentOver (Over.mk f) (Over.mk g)) →
      (E : ModuleDerived X) → (a b : ℤ) →
      (hE : ModuleDerived.HasTorAmplitudeInOver f E a b) →
      ModuleDerived.HasTorAmplitudeInOver f' ((ModuleDerived.pullback g').obj E) a b)

/- Lemma 75.20.7 (2): in a Tor-independent cartesian square of algebraic spaces,
a module flat over the base computes derived pullback at its degree-zero complex. -/
@[stacks 0DKD] #check
  (AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.computesAtSingle :
    {S : Scheme.{u}} → {X' X Y' Y : AlgebraicSpace S} →
      (g' : X' ⟶ X) → (f' : X' ⟶ Y') → (f : X ⟶ Y) → (g : Y' ⟶ Y) →
      (sq : IsPullback g' f' f g) →
      (hTor : TorIndependentOver (Over.mk f) (Over.mk g)) →
      (M : Modules X) → (hM : Modules.IsFlatOver M f) →
      Functor.LeftDerived.ComputesAt (Functor.Homotopy.toDerived (Modules.pullback g'))
        (HomotopyCategory.quasiIso (Modules X) (up ℤ))
        ((HomotopyCategory.singleFunctor (Modules X) 0).obj M))
