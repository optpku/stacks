module

import stacks_project.Chap78.Definition_78_11_1_Groupoid
import stacks_project.Chap66.Definition_66_4_1_Points
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Points
import stacks_project.Chap78.«78_20_0_1_Points»
import StacksCheckRecall

universe u

/- 78.20.0.1: given a scheme `S`, an algebraic space `B` over `S`, and a groupoid in
algebraic spaces `(U, R, s, t, c)` over `B`, the functor
`(Sch/S)_fppfᵒᵖ ⥤ Grpd` sends a scheme `S'` over `S` to the groupoid
`(U(S'), R(S'), s, t, c)` of scheme-valued `S`-points. The fppf decoration is the ambient
site `Scheme.fppfTopology.over S` on `Over S`. -/
@[stacks 044P] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.points :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
      {B : AlgebraicGeometry.AlgebraicSpace S},
      AlgebraicGeometry.GroupoidAlgebraicSpace B →
        CategoryTheory.Functor (CategoryTheory.Over S)ᵒᵖ
          CategoryTheory.Grpd.{u + 1, u + 1})
