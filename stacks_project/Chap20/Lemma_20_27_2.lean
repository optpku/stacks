module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 20.27.2: morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z` satisfy
`L(g)^* ⋙ L(f)^* = L((f ≫ g))^*` as functors `D(O_Z) ⟶ D(O_X)`, via the specified
derived-pullback composition comparison. This functor identity is expressed by invertibility
of the canonical composition comparison. -/
@[stacks 0D5S]
#check (AlgebraicGeometry.RingedSpace.modulePullbackDerived.compComparison_isIso f g :
    IsIso (AlgebraicGeometry.RingedSpace.modulePullbackDerived.compComparison f g))

end AlgebraicGeometry.RingedSpace

