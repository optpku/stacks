/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Quotient

/-! # Fundamental Chow classes -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- The fundamental Chow class of an integral algebraic space is the class of
its weight-one generic-point cycle in the intrinsic delta dimension. -/
def integralFundamentalClass [IsIntegral X] :
    chowGroup f δ (deltaDimension f δ (univIrreducibleClosed X)) :=
  chowMk f δ (deltaDimension f δ (univIrreducibleClosed X))
    ⟨integralFundamentalCycle f,
      integralSingleton_mem_cycleGroup f δ
        (deltaDimension f δ (univIrreducibleClosed X)) rfl⟩

/-- The fundamental Chow class is the quotient image of the integral
fundamental cycle. -/
theorem integralFundamentalClass_eq [IsIntegral X] :
    integralFundamentalClass f δ =
      chowMk f δ (deltaDimension f δ (univIrreducibleClosed X))
        ⟨integralFundamentalCycle f,
          integralSingleton_mem_cycleGroup f δ
            (deltaDimension f δ (univIrreducibleClosed X)) rfl⟩ := rfl

end AlgebraicGeometry.AlgebraicSpace.Hom
