/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Quotient

/-!
# The algebraic space 𝔸¹_k / ℤ

The quotient algebraic space and its canonical affine-line atlas are provided by
the shared quotient API.
-/

@[expose] public section

open CategoryTheory

universe u

/- Example 66.5.4: the affine-line quotient by integer translation. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.space :
  (k : Type u) → [Field k] → [CharZero k] →
    AlgebraicGeometry.AlgebraicSpace
      (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.base k))

#check (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.atlas :
  (k : Type u) → [Field k] → [CharZero k] →
    yoneda.obj (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k) ⟶
      (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.space k).functorOfPoints)
