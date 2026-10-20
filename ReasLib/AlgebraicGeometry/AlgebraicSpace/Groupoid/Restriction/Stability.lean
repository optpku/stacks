module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange

/-!
# Stability of restricted groupoids in algebraic spaces

This module records stability of local finite type, local finite presentation, and
flatness for the source and target maps of a restricted groupoid in algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
  {U' : Over B} (g : U' ⟶ G.U)

/-- If the source map, target map, and restriction morphism are locally of finite type,
then both structure maps of the restricted groupoid are locally of finite type. -/
theorem restrictionLocallyOfFiniteType
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    [AlgebraicSpace.LocallyOfFiniteType g.left] :
    AlgebraicSpace.LocallyOfFiniteType (G.pullback g).s.left ∧
      AlgebraicSpace.LocallyOfFiniteType (G.pullback g).t.left := sorry

/-- If the source map, target map, and restriction morphism are locally of finite
presentation, then both structure maps of the restricted groupoid are locally of
finite presentation. -/
theorem restrictionLocallyOfFinitePresentation
    [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.t.left]
    [AlgebraicSpace.LocallyOfFinitePresentation g.left] :
    AlgebraicSpace.LocallyOfFinitePresentation (G.pullback g).s.left ∧
      AlgebraicSpace.LocallyOfFinitePresentation (G.pullback g).t.left := sorry

/-- If the source map, target map, and restriction morphism are flat, then both
structure maps of the restricted groupoid are flat. -/
theorem restrictionFlat [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.Flat g.left] :
    AlgebraicSpace.Flat (G.pullback g).s.left ∧
      AlgebraicSpace.Flat (G.pullback g).t.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
