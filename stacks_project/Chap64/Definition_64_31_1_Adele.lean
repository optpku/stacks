/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.NumberTheory.FunctionField.Adele

open AlgebraicGeometry

/- The function-field adele API is owned by `ReasLib.NumberTheory.FunctionField.Adele`. -/
#check (AlgebraicGeometry.SchemeOverField.adeleRing :
    ∀ {k : Type*} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom], Type _)
