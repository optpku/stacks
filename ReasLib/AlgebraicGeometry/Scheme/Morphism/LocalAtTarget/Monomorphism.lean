/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf
public import Mathlib.CategoryTheory.MorphismProperty.Local

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Monomorphisms

/-- Monomorphisms of schemes are local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (MorphismProperty.monomorphisms AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.Monomorphisms
