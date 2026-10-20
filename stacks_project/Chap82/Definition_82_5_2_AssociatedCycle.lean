/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.componentMultiplicity :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X],
    (Y : ClosedSubspace X) → genericPoints Y.X → ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.associatedCycle :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X],
    (Y : ClosedSubspace X) → (Points X → ℤ) → ℤ →
      Function.locallyFinsupp (Points X) ℤ)
