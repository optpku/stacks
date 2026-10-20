/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.Polarized.Groupoids

/-!
# Polarized proper schemes over a base scheme

The costructured-arrow category of polarized proper schemes over a scheme is
bundled as a category fibred in groupoids over the slice category of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The projection from polarized proper schemes with a map to a base scheme
to the slice category over that scheme is fibred in groupoids. -/
instance instIsFiberedInGroupoids_toOver (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids (CostructuredArrow.toOver p S) :=
  sorry

/-- Polarized proper schemes with a map to `S`, bundled as a category fibred
in groupoids over `(Sch / S)_fppf`. -/
def toGroupoidsOver (S : Scheme.{u}) : GroupoidsOver S :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u}
    (CostructuredArrow.toOver p S)

/-- The projection of the bundled category of polarized proper schemes over
`S` is the canonical costructured-arrow projection to `Over S`. -/
theorem toGroupoidsOver_p (S : Scheme.{u}) :
    (toGroupoidsOver S).p = CostructuredArrow.toOver p S :=
  rfl

end AlgebraicGeometry.Polarized
