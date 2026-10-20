/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.WeilDivisor
public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Dimension

/-!
# Relative divisor cycles and Chow classes

This file refines the divisor cycle of a nonzero meromorphic section by its relative dimension
and records its class in the corresponding Chow group.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.MeromorphicSection

/-- The divisor cycle of a nonzero meromorphic section has the degree determined by the
relative dimension of the integral scheme. -/
theorem relativeDivisorCycle_mem
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    @Scheme.nonzeroMeromorphicSectionDivisorCycle X
        (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance ℒ inferInstance s hs ∈
      AlgebraicCycle.dimensionSubgroup (p.relativeDimensionFunction δ) k := sorry

/-- The degree-`k` divisor cycle associated to a nonzero meromorphic section of an invertible
module on an integral scheme. -/
noncomputable def relativeDivisorCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    CycleGroup X (p.relativeDimensionFunction δ) k :=
  ⟨@Scheme.nonzeroMeromorphicSectionDivisorCycle X
      (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance ℒ inferInstance s hs,
    relativeDivisorCycle_mem p δ ℒ s hs k hdim⟩

/-- Forgetting the degree of a relative divisor cycle recovers the existing algebraic divisor
cycle. -/
theorem relativeDivisorCycle_toAlgebraicCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (relativeDivisorCycle p δ ℒ s hs k hdim) =
      @Scheme.nonzeroMeromorphicSectionDivisorCycle X
        (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance ℒ inferInstance s hs := sorry

/-- The coefficient of a relative divisor cycle is the locally finite sum of the orders of the
section along prime divisors having the given generic point. -/
theorem relativeDivisorCycle_apply
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) (x : X) :
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (relativeDivisorCycle p δ ℒ s hs k hdim) x =
      ∑ᶠ Z : PrimeDivisor X,
        (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
          Z.genericPoint
            (@Scheme.nonzeroMeromorphicSectionWeilDivisorCoeff X
              (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
              ℒ inferInstance s hs Z)) x := sorry

/-- The degree-`k` Chow class represented by the divisor cycle of a nonzero meromorphic
section. -/
noncomputable def relativeDivisorClass
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k :=
  @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) inferInstance k
    (relativeDivisorCycle p δ ℒ s hs k hdim)

/-- A relative divisor class is the Chow class of its degree-refined divisor cycle. -/
theorem relativeDivisorClass_def
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    relativeDivisorClass p δ ℒ s hs k hdim =
      @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k
        (relativeDivisorCycle p δ ℒ s hs k hdim) := sorry

/-- The relative divisor class of an invertible module is independent of the chosen nonzero
meromorphic section. -/
theorem relativeDivisorClass_eq
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ]
    (s t : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : s ≠ 0) (ht : t ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    relativeDivisorClass p δ ℒ s hs k hdim =
      relativeDivisorClass p δ ℒ t ht k hdim := sorry

end AlgebraicGeometry.Scheme.Modules.MeromorphicSection
