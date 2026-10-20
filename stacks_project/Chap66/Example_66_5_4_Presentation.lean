/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Presentation

/-!
# Affine line modulo integer translation

The affine-line cover and integer-translation relation are provided by the shared
presentation API.
-/

@[expose] public section

universe u

/- Example 66.5.4: the base of the affine-line quotient presentation. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.base :
  (k : Type u) → [Field k] → [CharZero k] → AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover :
  (k : Type u) → [Field k] → [CharZero k] →
    CategoryTheory.Over (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.base k))

#check (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.preRelation :
  (k : Type u) → [Field k] → [CharZero k] →
    AlgebraicGeometry.Scheme.PreRelation
      (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k))
