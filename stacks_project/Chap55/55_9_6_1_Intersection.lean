module

public import ReasLib.AlgebraicGeometry.NumericalType.IntersectionForm

#check (NumericalType.intersectionForm :
  (T : NumericalType) → LinearMap.BilinForm ℤ (Fin T.n → ℤ))
#check (NumericalType.intersectionForm_isSymm :
  ∀ T : NumericalType, T.intersectionForm.IsSymm)
