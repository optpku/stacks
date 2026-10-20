module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineEtaleZariskiCover
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap66.Lemma_66_6_1_Cover

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.exists_affineEtaleZariskiCover :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    Nonempty (AlgebraicGeometry.AlgebraicSpace.AffineEtaleZariskiCover.{u} X))
