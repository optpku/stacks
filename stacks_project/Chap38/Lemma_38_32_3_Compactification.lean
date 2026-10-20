module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Category

universe u

#check (AlgebraicGeometry.Scheme.Compactification.interiorIsomorphisms :
  ∀ (S : AlgebraicGeometry.Scheme.{u}),
    CategoryTheory.MorphismProperty (AlgebraicGeometry.Scheme.Compactification S))
