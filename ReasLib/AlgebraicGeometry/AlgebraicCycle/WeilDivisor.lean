/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection

/-!
# Algebraic cycles associated to Weil divisors

This file turns a Weil divisor into the algebraic cycle supported at the generic points of its
prime divisors and applies that construction to divisors of nonzero meromorphic sections.
-/

@[expose] public section

open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry

namespace WeilDivisor

/-- The singleton cycles at the generic points of the prime divisors occurring in a Weil
divisor form a locally finite family. -/
theorem genericPointTermsLocallyFinite {X : Scheme.{u}} (D : Div(X)) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
        Z.genericPoint (D.coeff Z)).support := sorry

/-- Regard a Weil divisor as the algebraic cycle carrying its coefficient at the generic point
of each prime divisor. -/
noncomputable def toAlgebraicCycle {X : Scheme.{u}} (D : Div(X)) :
    AlgebraicCycle X ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun Z : PrimeDivisor X ↦
      @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
        Z.genericPoint (D.coeff Z))
    (genericPointTermsLocallyFinite D)

/-- The coefficient of the algebraic cycle of a Weil divisor is the locally finite sum of its
prime-divisor coefficients at the given point. -/
theorem toAlgebraicCycle_apply {X : Scheme.{u}} (D : Div(X)) (x : X) :
    toAlgebraicCycle D x =
      ∑ᶠ Z : PrimeDivisor X,
        (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
          Z.genericPoint (D.coeff Z)) x := sorry

/-- Conversion of Weil divisors to algebraic cycles commutes with integer scalar
multiplication. -/
theorem toAlgebraicCycle_zsmul {X : Scheme.{u}} (n : ℤ) (D : Div(X)) :
    toAlgebraicCycle (n • D) = n • toAlgebraicCycle D := sorry

end WeilDivisor

namespace Scheme

/-- The algebraic cycle associated to the Weil divisor of a nonzero meromorphic section of an
invertible module. -/
noncomputable def nonzeroMeromorphicSectionDivisorCycle
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0) :
    AlgebraicCycle X ℤ :=
  WeilDivisor.toAlgebraicCycle
    (nonzeroMeromorphicSectionWeilDivisor X ℒ s hs)

/-- The divisor cycle of a nonzero meromorphic section is obtained by converting its canonical
Weil divisor to an algebraic cycle. -/
theorem nonzeroMeromorphicSectionDivisorCycle_def
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0) :
    nonzeroMeromorphicSectionDivisorCycle X ℒ s hs =
      WeilDivisor.toAlgebraicCycle
        (nonzeroMeromorphicSectionWeilDivisor X ℒ s hs) := sorry

end Scheme

end AlgebraicGeometry
