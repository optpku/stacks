/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.WeilDivisor
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.OfGlobal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

/-!
# Fixed-dimension divisor cycles of global sections

This file associates a cycle in the expected relative dimension to a nonzero global section
of an invertible module and identifies its underlying algebraic cycle.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The divisor cycle of a nonzero global section has the expected relative degree. -/
theorem relativeNonzeroSectionDivisorCycle_mem
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    @Scheme.nonzeroMeromorphicSectionDivisorCycle X
        (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance ℒ inferInstance
        (toMeromorphicSection ℒ s) (toMeromorphicSection_ne_zero ℒ s hs) ∈
      AlgebraicCycle.dimensionSubgroup (p.relativeDimensionFunction δ) k := sorry

/-- The degree-`k` divisor cycle of a nonzero global section of an invertible module. -/
noncomputable def relativeNonzeroSectionDivisorCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    CycleGroup X (p.relativeDimensionFunction δ) k :=
  ⟨@Scheme.nonzeroMeromorphicSectionDivisorCycle X
      (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance ℒ inferInstance
      (toMeromorphicSection ℒ s) (toMeromorphicSection_ne_zero ℒ s hs),
    relativeNonzeroSectionDivisorCycle_mem p δ ℒ s hs k hdim⟩

/-- Forgetting the degree of the divisor cycle recovers the existing algebraic cycle. -/
theorem relativeNonzeroSectionDivisorCycle_toAlgebraicCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1) :
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (relativeNonzeroSectionDivisorCycle p δ ℒ s hs k hdim) =
      @Scheme.nonzeroMeromorphicSectionDivisorCycle X
        (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance ℒ inferInstance
        (toMeromorphicSection ℒ s) (toMeromorphicSection_ne_zero ℒ s hs) := sorry

end AlgebraicGeometry.Scheme.Modules
