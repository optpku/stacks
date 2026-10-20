module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Composition

/-!
# Relative dimension under composition of algebraic-space morphisms

Pointwise relative dimension is subadditive under composition of locally
finite type morphisms, with equality when the induced fibre map is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If locally finite type morphisms `f` and `g` have relative dimensions `d`
at `x` and `e` at its image, their composite has relative dimension at most
`d + e` at `x`. -/
theorem relativeDimensionLEAt_comp_add {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (d e : ℕ) (x : Points X)
    (hd : RelativeDimensionAt f d x)
    (he : RelativeDimensionAt g e (Points.map f x)) :
    RelativeDimensionLEAt (f ≫ g) (d + e) x :=
  sorry

/-- Relative dimensions of locally finite type morphisms add at a point when
the canonical map of fibres over a field-valued representative of its image
is flat at a lifting point. -/
theorem relativeDimensionAt_comp_add_of_flatAt_compFiberToBaseFiber
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (d e : ℕ) (x : Points X)
    (hd : RelativeDimensionAt f d x)
    (he : RelativeDimensionAt g e (Points.map f x))
    (p : FieldValuedPoint Z) (hp : Points.mk p = Points.map (f ≫ g) x)
    (x' : Points (pullbackAlongScheme (f ≫ g) p.hom))
    (hx' : Points.map (pullbackAlongScheme.fst (f ≫ g) p.hom) x' = x)
    (hflat : FlatAt (compFiberToBaseFiber f g p) x') :
    RelativeDimensionAt (f ≫ g) (d + e) x :=
  sorry

/-- Relative dimensions of locally finite type morphisms add at a point
where the first morphism is flat. -/
theorem relativeDimensionAt_comp_add_of_flatAt {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (d e : ℕ) (x : Points X)
    (hd : RelativeDimensionAt f d x)
    (he : RelativeDimensionAt g e (Points.map f x)) (hflat : FlatAt f x) :
    RelativeDimensionAt (f ≫ g) (d + e) x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
