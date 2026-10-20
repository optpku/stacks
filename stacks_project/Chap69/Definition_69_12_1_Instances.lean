module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category

/-! # Double-slice sheafification on the small étale site

The canonical coherent-module category owns the double-slice sheafification prerequisites.
-/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Coh.inclusion :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.Functor (AlgebraicGeometry.AlgebraicSpace.Coh X)
      (AlgebraicGeometry.AlgebraicSpace.Modules X))
