module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardProetale

@[expose] public section

universe u

#check
  (AlgebraicGeometry.StandardProetaleCover :
    ∀ (T : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine T], Type (u + 1))
