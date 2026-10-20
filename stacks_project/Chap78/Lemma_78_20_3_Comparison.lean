module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Comparison
public import stacks_project.Chap78.Lemma_78_20_2_Atlas

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceTarget :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
    AlgebraicGeometry.GroupoidAlgebraicSpace.atlasSource G ⟶
      AlgebraicGeometry.GroupoidAlgebraicSpace.atlasTarget G)
