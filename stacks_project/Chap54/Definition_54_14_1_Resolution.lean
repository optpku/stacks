module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution

open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.IsResolution :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ Y) →
    [AlgebraicGeometry.IsNoetherian Y] → [AlgebraicGeometry.IsIntegral Y] → Prop)
