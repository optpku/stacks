/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.SectionDivisor
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroCycle.Components
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroCycle.Grading

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Compatibility checks for meromorphic sections induced by global sections. -/
#check (AlgebraicGeometry.Scheme.Modules.toMeromorphicSection :
  ∀ {X : Scheme.{u}} (ℒ : X.Modules),
    ℒ.sections → X.toLocallyRingedSpace.meromorphicSections ℒ)

#check (AlgebraicGeometry.Scheme.Modules.toMeromorphicSection_ne_zero :
  ∀ {X : Scheme.{u}} (ℒ : X.Modules) [Invertible ℒ]
    (s : ℒ.sections), s ≠ 0 → toMeromorphicSection ℒ s ≠ 0)

/- Compatibility checks for fixed-dimension divisor cycles of global sections. -/
#check (AlgebraicGeometry.Scheme.Modules.relativeNonzeroSectionDivisorCycle_mem :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (hs : s ≠ 0)
    (k : ℤ) (_ : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
    @Scheme.nonzeroMeromorphicSectionDivisorCycle X
        (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance ℒ inferInstance
        (toMeromorphicSection ℒ s) (toMeromorphicSection_ne_zero ℒ s hs) ∈
      AlgebraicCycle.dimensionSubgroup (p.relativeDimensionFunction δ) k)

#check (AlgebraicGeometry.Scheme.Modules.relativeNonzeroSectionDivisorCycle :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (_ : s ≠ 0)
    (k : ℤ) (_ : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
    CycleGroup X (p.relativeDimensionFunction δ) k)

#check (AlgebraicGeometry.Scheme.Modules.relativeNonzeroSectionDivisorCycle_toAlgebraicCycle :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (hs : s ≠ 0)
    (k : ℤ) (hdim : p.relativeDimensionFunction δ (genericPoint X) = k + 1),
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (relativeNonzeroSectionDivisorCycle p δ ℒ s hs k hdim) =
      @Scheme.nonzeroMeromorphicSectionDivisorCycle X
        (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance ℒ inferInstance
        (toMeromorphicSection ℒ s) (toMeromorphicSection_ne_zero ℒ s hs))

/- Compatibility checks for fixed-dimension zero cycles of global sections. -/
#check (AlgebraicGeometry.Scheme.Modules.relativeZeroCycle_mem :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (k : ℤ),
    relativeZeroCycle p δ ℒ s k ∈
      AlgebraicCycle.dimensionSubgroup (p.relativeDimensionFunction δ) k)

#check (AlgebraicGeometry.Scheme.Modules.relativeZeroCycleGroup :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ] (_ : ℒ.sections) (k : ℤ),
    CycleGroup X (p.relativeDimensionFunction δ) k)

#check (AlgebraicGeometry.Scheme.Modules.relativeZeroCycleGroup_toAlgebraicCycle :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (k : ℤ),
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (relativeZeroCycleGroup p δ ℒ s k) =
      relativeZeroCycle p δ ℒ s k)

end AlgebraicGeometry.Scheme.Modules
