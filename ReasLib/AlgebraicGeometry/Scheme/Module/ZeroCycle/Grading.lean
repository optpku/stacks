/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroCycle

/-!
# Fixed-dimension zero cycles of sections

This file regards the relative zero cycle of a section as a cycle in its specified dimension
and relates the bundled cycle to its underlying algebraic cycle.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The relative zero cycle of a section is supported in its specified degree. -/
theorem relativeZeroCycle_mem
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (k : ℤ) :
    relativeZeroCycle p δ ℒ s k ∈
      AlgebraicCycle.dimensionSubgroup (p.relativeDimensionFunction δ) k := sorry

/-- The degree-`k` cycle of the zero scheme of a global section. -/
noncomputable def relativeZeroCycleGroup
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction δ) k :=
  ⟨relativeZeroCycle p δ ℒ s k, relativeZeroCycle_mem p δ ℒ s k⟩

/-- Forgetting the degree of the bundled zero cycle recovers the relative zero cycle. -/
theorem relativeZeroCycleGroup_toAlgebraicCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (k : ℤ) :
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (relativeZeroCycleGroup p δ ℒ s k) =
      relativeZeroCycle p δ ℒ s k := sorry

end AlgebraicGeometry.Scheme.Modules
