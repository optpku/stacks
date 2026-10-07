module

public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import stacks_project.Chap66.Definition_66_4_1_Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Points

/-! This compatibility module preserves the historical prerequisite imports. -/

open CategoryTheory AlgebraicGeometry

universe u

/- The promoted declaration remains available under its original fully qualified name. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.points :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
      {B : AlgebraicGeometry.AlgebraicSpace S},
      AlgebraicGeometry.GroupoidAlgebraicSpace B →
        CategoryTheory.Functor (CategoryTheory.Over S)ᵒᵖ
          CategoryTheory.Grpd.{u + 1, u + 1})
