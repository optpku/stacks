/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Affine
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange

/-!
# Modules on the affine objects of a category fibred in groupoids

The affine module category and the coefficient comparison are re-exported for
restriction to affine étale sites.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.GroupoidsOver.AffineModule :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), Type (u + 2))

#check (AlgebraicGeometry.GroupoidsOver.universeLiftForget₂Iso :
  CommRingCat.universeLift.{u, u + 1} ⋙
      forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ≅
    forget₂ CommRingCat.{u} RingCat.{u} ⋙
      Scheme.Site.ringUniverseLift.{u, u + 1})
