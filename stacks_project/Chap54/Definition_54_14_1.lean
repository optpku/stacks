module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution

open scoped AlgebraicGeometry

universe u

/- Definition 54.14.1: Let `Y` be a Noetherian integral scheme. A resolution of
singularities of `Y` is a modification `f : X ⟶ Y` such that `X` is regular. -/
@[stacks 0BGK] #check (AlgebraicGeometry.IsResolution :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ Y) →
    [AlgebraicGeometry.IsNoetherian Y] → [AlgebraicGeometry.IsIntegral Y] → Prop)
