/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier

/-!
# Effective Cartier divisors as bundled closed subspaces

A bundled closed subspace is an effective Cartier divisor exactly when the ideal
sheaf of its inclusion is invertible. The unit ideal defines the empty effective
Cartier divisor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The empty closed subspace, cut out by the unit ideal, is an effective Cartier
divisor. -/
theorem isEffectiveCartierDivisor_top {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsEffectiveCartierDivisor
      (ClosedSubspace.ofQuasiCoherentIdeal (⊤ : IdealSubobject X)).ι :=
  sorry

namespace ClosedSubspace

/-- A closed subspace is an effective Cartier divisor exactly when the ideal sheaf of
its inclusion is an invertible `𝒪_X`-module. -/
theorem isEffectiveCartierDivisor_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) :
    IsEffectiveCartierDivisor Z.ι ↔ isInvertibleObject (Hom.idealSheaf Z.ι) :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
