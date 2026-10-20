module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites

/-!
# Lisse-étale and flat-fppf site interfaces

These checks expose the algebraic-stack site interfaces to existing consumers.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleTopology :
  {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.GroupoidsOver S) →
    [AlgebraicGeometry.AlgebraicStack X] →
    CategoryTheory.GrothendieckTopology (AlgebraicGeometry.AlgebraicStack.lisseEtaleSite X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfTopology :
  {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.GroupoidsOver S) →
    [AlgebraicGeometry.AlgebraicStack X] →
    CategoryTheory.GrothendieckTopology (AlgebraicGeometry.AlgebraicStack.flatFppfSite X))
