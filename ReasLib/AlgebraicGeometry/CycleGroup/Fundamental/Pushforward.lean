/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary

/-!
# Proper pushforward of fundamental cycles

This file identifies proper pushforward of the fundamental cycle of an integral scheme with
the function-field-degree multiple of the target fundamental cycle.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- A proper dominant morphism between integral schemes of the same relative dimension sends
the source fundamental cycle to the function-field-degree multiple of the target fundamental
cycle. -/
theorem mapHom_fundamental_of_proper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (n : ℤ) (f : X ⟶ Y)
    [IsProper f.left] [IsDominant f.left]
    (hX : X.hom.relativeDimensionFunction δ (genericPoint X.left) = n)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n) :
    mapHom f.left (X.hom.relativeDimensionFunction δ)
        (Y.hom.relativeDimensionFunction δ) n
        (@fundamental X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) n) =
      (f.left.inducedFunctionFieldDegree : ℤ) •
        @fundamental Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction δ) n := sorry

end AlgebraicGeometry.CycleGroup
