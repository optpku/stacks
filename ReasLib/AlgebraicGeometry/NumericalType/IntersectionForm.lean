/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import ReasLib.AlgebraicGeometry.NumericalType

@[expose] public section

namespace NumericalType

/-- The integral bilinear form represented by a numerical type's intersection matrix. -/
public def intersectionForm (T : NumericalType) :
    LinearMap.BilinForm ℤ (Fin T.n → ℤ) :=
  Matrix.toBilin' T.intersection

/-- The bilinear form associated to a numerical type is symmetric. -/
public theorem intersectionForm_isSymm (T : NumericalType) :
    T.intersectionForm.IsSymm := sorry

end NumericalType
