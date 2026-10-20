/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

universe u

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.27.1
The construction above is independent of choices and defines an exact functor of
triangulated categories `L(f)^* : DerivedCategory (Modules Y) ⥤ DerivedCategory (Modules X)`.
Choice independence is through the canonical left-derived universal property and
computation on K-flat models, up to canonical isomorphism. -/
@[stacks 06YJ]
#check (AlgebraicGeometry.RingedSpace.modulePullbackDerived.isTriangulated :
  ∀ {X Y : AlgebraicGeometry.RingedSpace.{u}} (f : X ⟶ Y),
    (AlgebraicGeometry.RingedSpace.modulePullbackDerived f).IsTriangulatedWith
      (AlgebraicGeometry.RingedSpace.modulePullbackDerived.commShift f))

variable {X Y : AlgebraicGeometry.RingedSpace.{u}} (f : X ⟶ Y)

#check (AlgebraicGeometry.RingedSpace.modulePullbackDerived f :
  DerivedCategory (Modules Y) ⥤ DerivedCategory (Modules X))

#check (AlgebraicGeometry.RingedSpace.modulePullbackDerived.commShift f :
  (AlgebraicGeometry.RingedSpace.modulePullbackDerived f).CommShift ℤ)

#check (AlgebraicGeometry.RingedSpace.modulePullbackDerived.isLeftDerivedFunctor f :
  (AlgebraicGeometry.RingedSpace.modulePullbackDerived f).IsLeftDerivedFunctor
    ((AlgebraicGeometry.RingedSpace.modulePullbackToDerived f).totalLeftDerivedCounit
      DerivedCategory.Qh (AlgebraicGeometry.RingedSpace.ModuleQis Y))
    (AlgebraicGeometry.RingedSpace.ModuleQis Y))

end AlgebraicGeometry.RingedSpace
