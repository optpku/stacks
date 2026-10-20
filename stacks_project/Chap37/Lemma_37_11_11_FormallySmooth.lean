module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth

@[expose] public section

open CategoryTheory

universe u

/- Scheme-level formal smoothness is the property that every induced map on compatible
affine coordinate rings is formally smooth. -/
#check (AlgebraicGeometry.FormallySmooth :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ Y) → Prop)
