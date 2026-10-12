/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Cr
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The function field of a variety of dimension `r` over an algebraically closed
field is `C_r`. -/
theorem functionField_isCr_of_dimension {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Variety X] (r : ℕ)
    (h_dimension : X.dimension = r) :
    Field.IsCr X.left.functionField r := sorry

end AlgebraicGeometry.SchemeOverField
