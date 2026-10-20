module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.GermProperty

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAt_def :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (P : AlgebraicGeometry.GermProperty.{u})
    (hP : P.IsSmoothLocal) (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X] (x : AlgebraicGeometry.AlgebraicStack.Points X),
    AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAt P hP X x ↔
      AlgebraicGeometry.AlgebraicStack.existsSmoothAt P X x)
