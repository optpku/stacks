/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.IntersectionForm

#check (NumericalType.intersectionForm :
  (T : NumericalType) → LinearMap.BilinForm ℤ (Fin T.n → ℤ))
#check (NumericalType.intersectionForm_isSymm :
  ∀ T : NumericalType, T.intersectionForm.IsSymm)
