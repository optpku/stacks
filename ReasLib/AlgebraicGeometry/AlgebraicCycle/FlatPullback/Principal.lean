/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Dominant
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField.Units

/-!
# Flat pullback of principal cycles

This file records the compatibility of flat pullback with principal cycles and the
dimension support of the resulting cycle.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- Flat pullback carries a principal cycle to the principal cycle of the induced
function-field unit. -/
theorem flatPullback_principal
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (g : Y.left.functionFieldˣ) :
    flatPullback δ X Y f r (n + (r : ℤ) - 1)
        (@principal Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          inferInstance g) =
      @principal X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        inferInstance
        (f.left.functionFieldUnitsMap f.left.map_genericPoint_eq_of_isDominant g) := sorry

/-- The principal cycle obtained after flat pullback is supported in relative
`δ`-dimension `n + r - 1`. -/
theorem principal_pullback_mem_dimensionSubgroup
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (g : Y.left.functionFieldˣ) :
    @principal X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        inferInstance
        (f.left.functionFieldUnitsMap f.left.map_genericPoint_eq_of_isDominant g) ∈
      dimensionSubgroup (X.hom.relativeDimensionFunction δ)
        (n + (r : ℤ) - 1) := sorry

end AlgebraicGeometry.AlgebraicCycle
