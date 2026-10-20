/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian

/-!
# Locally Noetherian schemes over a base

The full subcategory of locally Noetherian objects of `Over S`, the induced
standard topology of the site `(Noetherian/S)_τ`, and restriction of
set-valued presheaves along the inclusion into `(Sch/S)_τ`.
-/

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.ObjectProperty

universe u

open AlgebraicGeometry.Scheme.Over

#check (AlgebraicGeometry.Scheme.Over.locallyNoetherian :
  ∀ (S : Scheme.{u}), ObjectProperty (Over S))

#check (AlgebraicGeometry.Scheme.Over.locallyNoetherian_iff :
  ∀ {S : Scheme.{u}} (X : Over S),
    locallyNoetherian S X ↔ IsLocallyNoetherian X.left)

#check (AlgebraicGeometry.StandardTopology.locallyNoetherianTopology :
  StandardTopology → ∀ (S : Scheme.{u}),
    GrothendieckTopology (locallyNoetherian S).FullSubcategory)

#check (AlgebraicGeometry.StandardTopology.restrictPresheaf :
  ∀ (S : Scheme.{u}), ((Over S)ᵒᵖ ⥤ Type (u + 1)) ⥤
    ((locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)))

#check (AlgebraicGeometry.StandardTopology.restrictPresheaf_obj :
  ∀ (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type (u + 1)),
    (AlgebraicGeometry.StandardTopology.restrictPresheaf S).obj F =
      (locallyNoetherian S).ι.op ⋙ F)
