module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback

/-! Compatibility facade for the regular-denominator pullback condition. -/

open CategoryTheory AlgebraicGeometry

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.PullbacksMeromorphicFunctionsDefined :
    {S : Scheme.{u}} → {X Y : AlgebraicGeometry.AlgebraicSpace S} → (X ⟶ Y) → Prop)
