module

public import ReasLib.AlgebraicGeometry.GroupoidScheme
import StacksCheckRecall

universe u

/- Definition 39.13.1 (1): A groupoid scheme over `S` consists of object and arrow schemes
over `S` whose induced category of `T`-points is a groupoid for every `T` over `S`. -/
@[stacks 0231] #check (AlgebraicGeometry.GroupoidScheme :
  (S : AlgebraicGeometry.Scheme.{u}) → Type (u + 1))

/- Definition 39.13.1 (2): A morphism of groupoid schemes is given by compatible maps on
objects and arrows, inducing functors between their groupoids of `T`-points. -/
@[stacks 0231] #check (AlgebraicGeometry.GroupoidScheme.Hom :
  {S : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.GroupoidScheme S → AlgebraicGeometry.GroupoidScheme S → Type u)
