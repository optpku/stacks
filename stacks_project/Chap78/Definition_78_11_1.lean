module

public import stacks_project.Chap78.Definition_78_11_1_Groupoid
import StacksCheckRecall

universe u

/- Definition 78.11.1 (1): A groupoid in algebraic spaces over `B` consists of object and
arrow algebraic spaces over `B` whose induced category of scheme-valued `T`-points is a
groupoid for every scheme `T` over `B`. -/
@[stacks 043W] #check (AlgebraicGeometry.GroupoidAlgebraicSpace :
  {S : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))

/- Definition 78.11.1 (2): A morphism of groupoids in algebraic spaces over `B` is given by
compatible maps on objects and arrows, inducing functors between their groupoids of
scheme-valued `T`-points. -/
@[stacks 043W] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom :
  {S : AlgebraicGeometry.Scheme.{u}} → {B : AlgebraicGeometry.AlgebraicSpace S} →
    AlgebraicGeometry.GroupoidAlgebraicSpace B →
      AlgebraicGeometry.GroupoidAlgebraicSpace B → Type (u + 1))
