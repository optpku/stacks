/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Hom

/-! # The category of formal objects -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

/-- Formal objects form a category with natural stage families as morphisms. -/
instance category : Category.{u} (FormalObject X) where
  toQuiver := ⟨fun ξ η ↦ NatTrans ξ.toFunctor η.toFunctor⟩
  id ξ := NatTrans.id ξ.toFunctor
  comp f g := NatTrans.vcomp f g
  id_comp f := Category.id_comp (obj := ℕ ⥤ X.total) f
  comp_id f := Category.comp_id (obj := ℕ ⥤ X.total) f
  assoc f g h := Category.assoc (obj := ℕ ⥤ X.total) f g h

end AlgebraicGeometry.GroupoidsOver.FormalObject
