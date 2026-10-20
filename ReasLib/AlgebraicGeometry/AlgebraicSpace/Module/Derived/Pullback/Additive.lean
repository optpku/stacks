module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Derived module pullback along any morphism of algebraic spaces is additive. -/
instance modulePullbackDerived.additive
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (modulePullbackDerived f).Additive := sorry

end AlgebraicGeometry.AlgebraicSpace
