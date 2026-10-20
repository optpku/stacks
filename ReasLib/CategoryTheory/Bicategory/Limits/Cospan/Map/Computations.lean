/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for mapped cospan transformations

This leaf exposes the five generator-level readouts of the concrete transformation map.  Keeping
these proposition-valued equations separate lets construction-only consumers depend only on
`Map.Basic`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u w' v' u'

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/- The following equations are the componentwise `1`-cell computations associated with the
walking-cospan presentation in Tag 003O. -/

/-- Mapping a cospan transformation maps its left component. -/
@[simp]
theorem map.left (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') :
    (map ψ P).left = P.map ψ.left := sorry

/-- Mapping a cospan transformation maps its right component. -/
@[simp]
theorem map.right (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') :
    (map ψ P).right = P.map ψ.right := sorry

/-- Mapping a cospan transformation maps its common-target component. -/
@[simp]
theorem map.base (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') :
    (map ψ P).base = P.map ψ.base := sorry

/-- The left comparison of a mapped cospan transformation is the canonical pseudofunctorial
pasting. -/
@[simp]
theorem map.leftIso (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') :
    (map ψ P).leftIso =
      (P.mapComp ψ.left f').symm ≪≫ P.map₂Iso ψ.leftIso ≪≫
        P.mapComp f ψ.base := sorry

/-- The right comparison of a mapped cospan transformation is the canonical pseudofunctorial
pasting. -/
@[simp]
theorem map.rightIso (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') :
    (map ψ P).rightIso =
      (P.mapComp ψ.right g').symm ≪≫ P.map₂Iso ψ.rightIso ≪≫
        P.mapComp g ψ.base := sorry

end CategoryTheory.Bicategory.CospanTransform
