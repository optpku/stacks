/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Deformation.SquareZero

/-!
# Compatibility bridge for square-zero deformation kernels

The reusable square-zero deformation API is owned by
`ReasLib.AlgebraicGeometry.Deformation.SquareZero`.
-/

@[expose] public section

open AlgebraicGeometry.Deformation

universe u

/- The kernel carrier used by the square-zero deformation API. -/
#check (kernelModule : {A A' : Type u} → [CommRing A] → [CommRing A'] →
  (π : A' →+* A) → [π.IsSquareZeroExtension] → Type u)
