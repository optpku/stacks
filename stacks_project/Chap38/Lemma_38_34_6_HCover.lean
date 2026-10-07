module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Comparison

universe u v

#check
  (AlgebraicGeometry.Scheme.HCovering :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v},
      (ι → CategoryTheory.Over T) → Prop)
