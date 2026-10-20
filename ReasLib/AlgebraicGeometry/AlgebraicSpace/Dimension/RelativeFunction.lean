/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The relative dimension function adds the canonical residue-field
transcendence degree to the dimension at the image point. -/
noncomputable abbrev relativeDimensionFunction {S : Scheme.{u}}
    {B X : AlgebraicSpace S} (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) : Points X → ℤ :=
  fun x ↦ δ (Points.map f x) + (residueFieldTrdegAt f x : ℤ)

/-- Evaluation uses the existing point map and residue-field invariant. -/
theorem relativeDimensionFunction_apply {S : Scheme.{u}}
    {B X : AlgebraicSpace S} (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) (x : Points X) :
    relativeDimensionFunction f δ x =
      δ (Points.map f x) + (residueFieldTrdegAt f x : ℤ) := sorry

/-- Relative dimension functions compose along locally finite-type morphisms. -/
theorem relativeDimensionFunction_comp {S : Scheme.{u}}
    {X Y B : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ B)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (δ : Points B → ℤ) :
    relativeDimensionFunction (f ≫ g) δ =
      relativeDimensionFunction f (relativeDimensionFunction g δ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
