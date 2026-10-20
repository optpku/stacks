/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Prime
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.HenselianFraction

/-! # Henselian local rings at generic points of prime divisors -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [h_locallyNoetherian : IsLocallyNoetherian X] [h_integral : IsIntegral X]

include h_locallyNoetherian h_integral

/-- The henselian local ring at a prime-divisor generic point is reduced. -/
instance instIsReduced_henselianLocalRing_genericPoint (Z : PrimeDivisor X) :
    _root_.IsReduced (henselianLocalRing X Z.genericPoint) := by
  let _ := h_locallyNoetherian
  sorry

/-- The henselian local ring at a prime-divisor generic point is Noetherian. -/
instance instIsNoetherianRing_henselianLocalRing_genericPoint (Z : PrimeDivisor X) :
    IsNoetherianRing (henselianLocalRing X Z.genericPoint) := by
  let _ := h_locallyNoetherian
  sorry

/-- The henselian local ring at a prime-divisor generic point has Krull dimension one. -/
theorem ringKrullDim_henselianLocalRing_genericPoint (Z : PrimeDivisor X) :
    ringKrullDim (henselianLocalRing X Z.genericPoint) = 1 := by
  sorry

/-- The henselian local ring at a prime-divisor generic point is reduced, Noetherian,
local, and one-dimensional, and the function field embeds in its total quotient ring. -/
theorem henselianLocalRing_genericPoint_spec (Z : PrimeDivisor X) :
    _root_.IsReduced (henselianLocalRing X Z.genericPoint) ∧
      IsNoetherianRing (henselianLocalRing X Z.genericPoint) ∧
      IsLocalRing (henselianLocalRing X Z.genericPoint) ∧
      ringKrullDim (henselianLocalRing X Z.genericPoint) = 1 ∧
      Function.Injective (rationalFunctionToHenselianFraction Z.genericPoint) := by
  exact ⟨inferInstance, inferInstance, inferInstance,
    ringKrullDim_henselianLocalRing_genericPoint Z,
    rationalFunctionToHenselianFraction_injective Z.genericPoint⟩

/-- The henselian local ring at a prime-divisor generic point has Krull dimension at most one. -/
instance instKrullDimLE_one_henselianLocalRing_genericPoint (Z : PrimeDivisor X) :
    Ring.KrullDimLE 1 (henselianLocalRing X Z.genericPoint) := by
  rw [Ring.krullDimLE_iff]
  simp [ringKrullDim_henselianLocalRing_genericPoint Z]

end AlgebraicGeometry.AlgebraicSpace
