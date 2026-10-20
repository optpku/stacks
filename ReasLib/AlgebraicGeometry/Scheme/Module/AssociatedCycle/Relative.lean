/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary

/-!
# Relative associated cycles

This file grades the associated cycle of a coherent module by the dimension
function induced by a morphism to a universally catenary base.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The degree-`k` associated cycle of a coherent module, measured by the
relative dimension function of a morphism. -/
noncomputable def relativeAssociatedCycle
    {X S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [hF : F.IsCoherent] (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction δ) k :=
  ⟨@associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian p) F hF
      (p.relativeDimensionFunction δ) k,
    @associatedCycle_mem_dimensionSubgroup X
      (LocallyOfFiniteType.isLocallyNoetherian p) F hF
      (p.relativeDimensionFunction δ) k⟩

/-- Forgetting the grading of a relative associated cycle recovers the
coherent module's associated algebraic cycle coefficientwise. -/
theorem relativeAssociatedCycle_toAlgebraicCycle
    {X S : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [hF : F.IsCoherent] (k : ℤ) (x : X) :
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (relativeAssociatedCycle p δ F k) x =
      @associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian p) F hF
        (p.relativeDimensionFunction δ) k x := sorry

end AlgebraicGeometry.Scheme.Modules
