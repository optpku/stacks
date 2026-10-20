/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.IntersectionForm

#check (NumericalType.intersectionForm :
  (T : NumericalType) → LinearMap.BilinForm ℤ (Fin T.n → ℤ))
#check (NumericalType.intersectionForm_isSymm :
  ∀ T : NumericalType, T.intersectionForm.IsSymm)
