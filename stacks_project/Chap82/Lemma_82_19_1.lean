/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback.MeromorphicSection
import StacksCheckRecall

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function Set Topology
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.19.1. Flat pullback of the divisor of a nonzero meromorphic section
is the locally finite multiplicity-weighted sum of the component divisors. -/
@[stacks 0EQQ] #check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_meromorphicSectionDivisor :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s),
    flatPullback pY pX δ f r hf (n - 1)
        (meromorphicSectionDivisorCycle pY δ s hs) =
      AlgebraicCycle.locallyFiniteSum
        (fun η : genericPoints X ↦
          flatComponentMeromorphicDivisor pY pX δ f r hf L s hs η)
        (locallyFinite_flatComponentMeromorphicDivisor pY pX δ f r hf L s hs))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_meromorphicSectionDivisor_mem_cycleGroup :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s),
    flatPullback pY pX δ f r hf (n - 1)
        (meromorphicSectionDivisorCycle pY δ s hs) ∈
      (cycleGroup pX) δ (n + (r : ℤ) - 1))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatComponentMeromorphicDivisorSum_mem_cycleGroup :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s),
    AlgebraicCycle.locallyFiniteSum
        (fun η : genericPoints X ↦
          flatComponentMeromorphicDivisor pY pX δ f r hf L s hs η)
        (locallyFinite_flatComponentMeromorphicDivisor pY pX δ f r hf L s hs) ∈
      (cycleGroup pX) δ (n + (r : ℤ) - 1))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatComponent_deltaDimension :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (η : genericPoints X),
    @deltaDimension S B (flatComponent pX η).X inferInstance inferInstance
      ((flatComponent pX η).ι ≫ pX) (quasiSeparated_flatComponent_structure pX η)
      (locallyOfFiniteType_flatComponent_structure pX η) δ inferInstance
      (@univIrreducibleClosed S (flatComponent pX η).X (isIntegral_flatComponent pX η)) = n + (r : ℤ))

