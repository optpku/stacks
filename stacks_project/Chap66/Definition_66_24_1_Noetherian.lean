module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import stacks_project.Chap65.Definition_65_6_3_Hom

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
