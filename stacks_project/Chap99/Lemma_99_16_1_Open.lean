/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.NegativeExt

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open scoped DerivedExt

noncomputable section

universe u

/- Derived base-change compatibility API. -/
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.negativeExtVanishing :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (K E : ModuleDerived X)
    (hK : IsPseudoCoherent X K) (hE : IsPerfectRelativeTo f E),
    OpenSubspace Y)
