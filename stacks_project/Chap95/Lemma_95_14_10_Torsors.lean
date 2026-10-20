module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.Category
public import stacks_project.Chap78.Lemma_78_5_2

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GroupAlgebraicSpace.Torsors.forget :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B),
    AlgebraicGeometry.GroupAlgebraicSpace.Torsors.Obj G ⥤ Over S)
