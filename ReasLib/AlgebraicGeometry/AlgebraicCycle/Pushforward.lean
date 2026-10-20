module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.AlgebraicCycle

/-- Proper pushforward of algebraic cycles is compatible with composition for the relative
dimension functions induced from a common universally catenary base. -/
theorem map_comp_of_proper {R : Type v} [Semiring R]
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y Z : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] (c : AlgebraicCycle X.left R) :
    map g.left (Y.hom.relativeDimensionFunction δ) (Z.hom.relativeDimensionFunction δ)
        (map f.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) c) =
      map (f.left ≫ g.left) (X.hom.relativeDimensionFunction δ)
        (Z.hom.relativeDimensionFunction δ) c := sorry

/-- Proper pushforward on integer cycles of a fixed relative dimension is compatible with
composition. -/
theorem map_comp_on_dimensionSubgroup_of_proper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y Z : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] (k : ℤ) :
    (fun c : dimensionSubgroup (X.hom.relativeDimensionFunction δ) k ↦
      map g.left (Y.hom.relativeDimensionFunction δ) (Z.hom.relativeDimensionFunction δ)
        (map f.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) (c : AlgebraicCycle X.left ℤ))) =
      fun c : dimensionSubgroup (X.hom.relativeDimensionFunction δ) k ↦
        map (f.left ≫ g.left) (X.hom.relativeDimensionFunction δ)
        (Z.hom.relativeDimensionFunction δ) (c : AlgebraicCycle X.left ℤ) := sorry

end AlgebraicGeometry.AlgebraicCycle
