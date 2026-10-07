module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyReduced

universe u

open CategoryTheory

#check (AlgebraicGeometry.Scheme.Hom.geometricallyReducedFiberLocus :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}}, (f : X ⟶ Y) → Set Y)
