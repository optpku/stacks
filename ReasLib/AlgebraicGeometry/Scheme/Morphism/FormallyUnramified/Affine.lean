/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace FormallyUnramified

/-- A formally unramified morphism between affine schemes is characterized by the
formally unramified map induced on global sections. -/
theorem iff_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S] :
    AlgebraicGeometry.FormallyUnramified f ↔ f.appTop.hom.FormallyUnramified :=
  HasRingHomProperty.iff_of_isAffine

end FormallyUnramified

end AlgebraicGeometry
