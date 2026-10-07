module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Operations

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/-!
# Lemma 29.28.2

Composition formulas for local fibre dimension are maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Operations`.
-/

/- Lemma 29.28.2: local fibre dimensions are subadditive under composition of
locally finite type scheme morphisms. -/
@[stacks 02JS] #check
  (AlgebraicGeometry.Scheme.Hom.fiberDimensionAt_comp_le :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X),
      (f ≫ g).fiberDimensionAt x ≤ f.fiberDimensionAt x + g.fiberDimensionAt (f x))

#check
  (AlgebraicGeometry.Scheme.Hom.fiberDimensionAt_comp_eq_add_of_flatAt_compFiberToBaseFiber :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X)
      (hflat : Scheme.Hom.flatAt (Scheme.Hom.compFiberToBaseFiber f g (g (f x)))
        ((f ≫ g).asFiber x)),
      (f ≫ g).fiberDimensionAt x = f.fiberDimensionAt x + g.fiberDimensionAt (f x))

#check
  (AlgebraicGeometry.Scheme.Hom.flatAt_compFiberToBaseFiber_of_flatAt :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
      (hflat : Scheme.Hom.flatAt f x),
      Scheme.Hom.flatAt (Scheme.Hom.compFiberToBaseFiber f g (g (f x)))
        ((f ≫ g).asFiber x))

#check
  (AlgebraicGeometry.Scheme.Hom.fiberDimensionAt_comp_eq_add_of_flatAt :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X)
      (hflat : Scheme.Hom.flatAt f x),
      (f ≫ g).fiberDimensionAt x = f.fiberDimensionAt x + g.fiberDimensionAt (f x))
