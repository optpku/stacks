module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle

universe u

#check (AlgebraicGeometry.Scheme.IdealSheafData.associatedCycle :
  {X : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsLocallyNoetherian X] →
    (Z : X.IdealSheafData) → (d : X → ℤ) → (k : ℤ) →
      AlgebraicGeometry.CycleGroup X d k)
