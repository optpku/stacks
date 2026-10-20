module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap99.Lemma_99_13_1_Spaces

universe u

/-! Families of curves and their inclusion use the canonical algebraic-space category. -/
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.inclusion :
  ∀ S : AlgebraicGeometry.Scheme.{u},
    CategoryTheory.Functor
      (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.Obj S)
      (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids S))
