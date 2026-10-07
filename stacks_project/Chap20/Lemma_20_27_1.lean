module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.27.1
The construction above is independent of choices and defines an exact functor of
triangulated categories `L(f)^* : DerivedCategory (Modules Y) ⥤ DerivedCategory (Modules X)`. -/
@[stacks 06YJ]
#check @modulePullbackDerived.isTriangulated

#check @modulePullbackDerived
#check @modulePullbackDerived.commShift

end AlgebraicGeometry.RingedSpace
