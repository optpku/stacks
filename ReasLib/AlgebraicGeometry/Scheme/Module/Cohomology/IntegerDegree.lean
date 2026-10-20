/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}}

/-- The dimension of ordinary scheme-module cohomology in an integer degree, extended by zero
in negative degrees. -/
def cohomologyFinrankInt
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (i : ℤ) : ℕ :=
  if 0 ≤ i then cohomologyFinrank f F i.toNat else 0

/-- In a nonnegative degree, integer-degree cohomology finrank agrees with ordinary cohomology
finrank. -/
theorem cohomologyFinrankInt_of_nonneg
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (i : ℤ) (hi : 0 ≤ i) :
    cohomologyFinrankInt f F i = cohomologyFinrank f F i.toNat := sorry

/-- In a negative degree, integer-degree cohomology finrank vanishes. -/
theorem cohomologyFinrankInt_of_neg
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (i : ℤ) (hi : i < 0) :
    cohomologyFinrankInt f F i = 0 := sorry

end AlgebraicGeometry.Scheme.Hom
