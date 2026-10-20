/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom functor for full-subbicategory two-fibre-product maps

The map and `2`-cell actions assembled into a functor, together with its action on
isomorphisms.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]
variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : P.FullSubbicategory}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}
variable {psi phi : CospanTransform F₁ G₁ F₂ G₂}

/-- Explicit two-fibre-product maps are functorial in transformations and modifications between
each fixed pair of cospans in the full subbicategory. -/
@[stacks 0040 "hom functor of the full-subbicategory two-fibre-product action"]
noncomputable def mapFunctor :
    CospanTransform F₁ G₁ F₂ G₂ ⥤
      (apex F₁ G₁ ⟶ apex F₂ G₂) where
  obj := map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

/-- The object action of the explicit two-fibre-product hom functor is `map`. -/
@[simp]
theorem mapFunctor.obj (psi : CospanTransform F₁ G₁ F₂ G₂) :
    mapFunctor.obj psi = map psi := sorry

/-- The morphism action of the explicit two-fibre-product hom functor is `map₂`. -/
@[simp]
theorem mapFunctor.map
    (Gamma : Pseudofunctor.StrongTrans.Hom psi phi) :
    mapFunctor.map Gamma = map₂ Gamma := sorry

/-- An isomorphism of cospan transformations induces an isomorphism between the corresponding
explicit two-fibre-product maps. -/
@[stacks 0040 "isomorphism of full-subbicategory two-fibre-product maps"]
noncomputable def map.iso (e : psi ≅ phi) :
    map psi ≅ map phi :=
  mapFunctor.mapIso e

/-- The forward component of an induced two-fibre-product map isomorphism is the image of the
forward cospan modification. -/
@[simp]
theorem map.iso.hom (e : psi ≅ phi) :
    (map.iso e).hom = map₂ e.hom := sorry

/-- The inverse component of an induced two-fibre-product map isomorphism is the image of the
inverse cospan modification. -/
@[simp]
theorem map.iso.inv (e : psi ≅ phi) :
    (map.iso e).inv = map₂ e.inv := sorry

end TwoFibreProduct

end CategoryTheory
