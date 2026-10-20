/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern
public import ReasLib.AlgebraicGeometry.ChowGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental

/-!
# First Chern classes and divisor classes

This file identifies first-Chern intersection with the fundamental cycle with the Chow class
of the divisor of a nonzero meromorphic section.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The Chow class of the divisor of any nonzero meromorphic section of an invertible module
is the first Chern class capped with the fundamental cycle. -/
theorem firstChernClassCap_fundamental_eq_divisorClass
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    firstChernClassCap p δ ℒ k
        (@CycleGroup.fundamental X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) (k + 1)) =
      MeromorphicSection.relativeDivisorClass p δ ℒ s hs k hdim := sorry

end AlgebraicGeometry.Scheme.Modules
