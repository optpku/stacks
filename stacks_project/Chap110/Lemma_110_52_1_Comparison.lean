module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.Comparison

/-! # Viewing fppf torsors as principal homogeneous spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.GroupAlgebraicSpace.toPrincipal :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B),
    GroupAlgebraicSpace.Torsors.stack G ⟶ GroupAlgebraicSpace.Principal.stack G)

#check (AlgebraicGeometry.GroupScheme.toPrincipal :
  ∀ {S : Scheme.{u}} (G : GroupScheme S),
    GroupAlgebraicSpace.Torsors.stack (GroupScheme.toGroupAlgebraicSpace G) ⟶
      GroupAlgebraicSpace.Principal.stack (GroupScheme.toGroupAlgebraicSpace G))
