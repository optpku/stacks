/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Irreducible

/-! # Fundamental cycles of integral algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable [IsQuasiSeparated B]
variable (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
variable [IsIntegral X]

/-- The integral fundamental cycle has weight one at the generic point of the whole space. -/
noncomputable def integralFundamentalCycle : Function.locallyFinsupp (Points X) ℤ :=
  @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
    (genericPoint_of_good pX (univIrreducibleClosed X)) 1

open Classical in
/-- The coefficient of the integral fundamental cycle is one at the generic point
and zero at every other point. -/
theorem integralFundamentalCycle_apply (x : Points X) :
    integralFundamentalCycle pX x =
      if x = genericPoint_of_good pX (univIrreducibleClosed X) then 1 else 0 := by
  simp only [integralFundamentalCycle, Function.locallyFinsuppWithin.single_apply]

/-- The fundamental cycle of an integral space of delta dimension `n` is an `n`-cycle. -/
theorem integralSingleton_mem_cycleGroup [UniversallyCatenary B]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (n : ℤ)
    (hX : deltaDimension pX δ (univIrreducibleClosed X) = n) :
    integralFundamentalCycle pX ∈ cycleGroup pX δ n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
