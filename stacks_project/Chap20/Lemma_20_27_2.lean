/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
derived-pullback composition comparison and its invertibility. -/
@[stacks 0D5S "derived pullback composition comparison"]
#check (modulePullbackDerived.compComparison f g :
    L(g)^* ⋙ L(f)^* ⟶ L((f ≫ g))^*)

@[stacks 0D5S "derived pullback composition comparison is invertible"]
#check (modulePullbackDerived.compComparison_isIso f g :
    IsIso (modulePullbackDerived.compComparison f g))

@[stacks 0D5S "derived pullback composition isomorphism"]
#check @modulePullbackDerived.compIso

@[stacks 0D5S "derived pullback composition isomorphism forward map"]
#check @modulePullbackDerived.compIso_hom

@[stacks 0D5S "derived pullback composition proof independence"]
#check @modulePullbackDerived.compIso_eq

end AlgebraicGeometry.RingedSpace

