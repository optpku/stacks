module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical

@[expose] public section

universe u

namespace AlgebraicGeometry.Isomorphisms

/-- Isomorphisms of schemes are local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (CategoryTheory.MorphismProperty.isomorphisms AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage :=
  CategoryTheory.Precoverage.ZeroHypercover.instIsLocalAtTargetIsomorphisms

end AlgebraicGeometry.Isomorphisms
