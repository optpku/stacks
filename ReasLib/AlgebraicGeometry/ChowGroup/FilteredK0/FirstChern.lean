/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FilteredK0.Image
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.DenominatorProduct
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.SupportDimension.Tensor

/-!
# Invertible tensor twists in filtered K-theory

This file relates the change in a filtered Grothendieck class under tensoring by an
invertible module to the corresponding first Chern class action on Chow groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.FilteredK0

/-- The filtered Grothendieck class of an invertible tensor twist minus the original
class. -/
noncomputable def tensorDifference
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (L : X.Modules) [Invertible L]
    (F : RingedSpace.CohLE X.toRingedSpace (p.relativeDimensionFunction δ) (k + 1)) :
    FilteredK0 p δ (k + 1) (k - 1) := by
  -- Local instance justification (proof-local temporary data): tensorInvertible needs the instance derived from p.
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  exact
    of p δ (k + 1) (k - 1)
        (RingedSpace.CohLE.tensorInvertible (p.relativeDimensionFunction δ) (k + 1) F L) -
      of p δ (k + 1) (k - 1) F

/-- The tensor-difference class is the difference of the two indicated filtered
Grothendieck classes. -/
theorem tensorDifference_def
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (L : X.Modules) [Invertible L]
    (F : RingedSpace.CohLE X.toRingedSpace (p.relativeDimensionFunction δ) (k + 1)) :
    tensorDifference p δ k L F =
      (by
        -- Local instance justification (proof-local temporary data): tensorInvertible needs the instance derived from p.
        letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
        exact
          of p δ (k + 1) (k - 1)
              (RingedSpace.CohLE.tensorInvertible
                (p.relativeDimensionFunction δ) (k + 1) F L) -
            of p δ (k + 1) (k - 1) F) := sorry

/-- The canonical Chow class of the first Chern action is the filtered Grothendieck
class change induced by the corresponding invertible tensor twist. -/
theorem toFilteredK0_firstChernClassCap
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (L : X.Modules) [Invertible L]
    (F : RingedSpace.CohLE X.toRingedSpace (p.relativeDimensionFunction δ) (k + 1)) :
    ChowGroup.toFilteredK0 p δ k
        (firstChernClassCap p δ L k (GradedK0.objectCycle p δ (k + 1) F)) =
      tensorDifference p δ k L F := sorry

/-- The filtered Grothendieck class change induced by an invertible tensor twist lies
in the image of the degree-`k` graded Grothendieck group. -/
theorem tensorDifference_mem_filteredImage
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (L : X.Modules) [Invertible L]
    (F : RingedSpace.CohLE X.toRingedSpace (p.relativeDimensionFunction δ) (k + 1)) :
    tensorDifference p δ k L F ∈ GradedK0.filteredImage p δ k := sorry

end AlgebraicGeometry.Scheme.Modules.FilteredK0
