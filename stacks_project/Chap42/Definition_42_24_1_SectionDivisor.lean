/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.WeilDivisor

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- The divisor cycle of a nonzero meromorphic section has the expected relative degree. -/
#check (AlgebraicGeometry.Scheme.Modules.MeromorphicSection.relativeDivisorCycle_mem :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
      (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
    @Scheme.nonzeroMeromorphicSectionDivisorCycle X
        (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance ℒ inferInstance s hs ∈
      AlgebraicCycle.dimensionSubgroup (p.relativeDimensionFunction δ) k)

/- A nonzero meromorphic section determines a cycle in the expected relative degree. -/
#check (AlgebraicGeometry.Scheme.Modules.MeromorphicSection.relativeDivisorCycle :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
      (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
    CycleGroup X (p.relativeDimensionFunction δ) k)

/- Forgetting the relative degree recovers the ungraded divisor cycle. -/
#check (AlgebraicGeometry.Scheme.Modules.MeromorphicSection.relativeDivisorCycle_toAlgebraicCycle :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
      (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (Scheme.Modules.MeromorphicSection.relativeDivisorCycle p δ ℒ s hs k hdim) =
      @Scheme.nonzeroMeromorphicSectionDivisorCycle X
        (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance ℒ inferInstance s hs)

/- The coefficients of the relative divisor cycle are the orders along prime divisors. -/
#check (AlgebraicGeometry.Scheme.Modules.MeromorphicSection.relativeDivisorCycle_apply :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
      (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) (x : X),
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (Scheme.Modules.MeromorphicSection.relativeDivisorCycle p δ ℒ s hs k hdim) x =
      ∑ᶠ Z : PrimeDivisor X,
        (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
          Z.genericPoint
            (@Scheme.nonzeroMeromorphicSectionWeilDivisorCoeff X
              (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
              ℒ inferInstance s hs Z)) x)

/- A nonzero meromorphic section determines a class in the expected Chow group. -/
#check (AlgebraicGeometry.Scheme.Modules.MeromorphicSection.relativeDivisorClass :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
      (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k)

/- The relative divisor class is represented by the relative divisor cycle. -/
#check (AlgebraicGeometry.Scheme.Modules.MeromorphicSection.relativeDivisorClass_def :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
      (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
    Scheme.Modules.MeromorphicSection.relativeDivisorClass p δ ℒ s hs k hdim =
      @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k
        (Scheme.Modules.MeromorphicSection.relativeDivisorCycle p δ ℒ s hs k hdim))

/- The relative divisor class does not depend on the chosen nonzero meromorphic section. -/
#check (AlgebraicGeometry.Scheme.Modules.MeromorphicSection.relativeDivisorClass_eq :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
      (s t : X.toLocallyRingedSpace.meromorphicSections ℒ)
      (hs : s ≠ 0) (ht : t ≠ 0)
      (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
    Scheme.Modules.MeromorphicSection.relativeDivisorClass p δ ℒ s hs k hdim =
      Scheme.Modules.MeromorphicSection.relativeDivisorClass p δ ℒ t ht k hdim)
