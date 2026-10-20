/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.CycleGroup.SectionDivisor
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroCycle.Grading

/-!
# First Chern classes and zero schemes of sections

This file identifies the divisor cycle of a nonzero global section with its zero-scheme cycle
and computes the corresponding first-Chern cap class.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The divisor cycle of a nonzero global section equals the cycle of its zero scheme. -/
theorem divisorCycle_eq_zeroCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    relativeNonzeroSectionDivisorCycle p δ ℒ s hs k hdim =
      relativeZeroCycleGroup p δ ℒ s k := sorry

/-- Capping the fundamental cycle with the first Chern class of an invertible module gives
the Chow class of the zero scheme of any nonzero global section. -/
theorem firstChernClassCap_fundamental_eq_zeroCycleClass
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    firstChernClassCap p δ ℒ k
        (@CycleGroup.fundamental X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) (k + 1)) =
      @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k
        (relativeZeroCycleGroup p δ ℒ s k) := sorry

end AlgebraicGeometry.Scheme.Modules
