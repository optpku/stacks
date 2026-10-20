/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of the local `2`-cell action of based inertia

This file owns the component, induced based `2`-morphism, local hom functor, and action on
isomorphisms. Projection computations and whiskering laws are layered separately.
-/

@[expose] public section

universe u v u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace Inertia

variable {X : BasedCategory.{v₁, u₁} C}
variable {Y : BasedCategory.{v₂, u₂} C}
variable {Z : BasedCategory.{v₃, u₃} C}
variable {F G H : X ⥤ᵇ Y}

namespace map₂

/-- A component of the original based `2`-morphism intertwines the induced automorphisms. -/
@[stacks 04Z4 "inertia two-cell component compatibility"]
theorem component.comm (η : F ⟶ G) (A : (inertia X).obj) :
    ((map F).toFunctor.obj A).aut.hom ≫ η.toNatTrans.app A.obj =
      η.toNatTrans.app A.obj ≫ ((map G).toFunctor.obj A).aut.hom := sorry

/-- The component of the inertia action on a based `2`-morphism. -/
@[stacks 04Z4 "component of the based inertia action on 2-morphisms"]
def component (η : F ⟶ G) (A : (inertia X).obj) :
    (map F).toFunctor.obj A ⟶ (map G).toFunctor.obj A :=
  CategoryTheory.RelativeInertia.homMk Y.p (η.toNatTrans.app A.obj)
    (component.comm η A)

/-- The canonical components induced by a based `2`-morphism are natural in inertia
morphisms. -/
@[reassoc, stacks 04Z4 "inertia two-cell component naturality"]
theorem component.naturality (η : F ⟶ G)
    {A B : (inertia X).obj} (φ : A ⟶ B) :
    (map F).toFunctor.map φ ≫ component η B =
      component η A ≫ (map G).toFunctor.map φ := sorry

/-- Each canonical component induced by a based `2`-morphism is vertical over the unchanged
base. -/
@[stacks 04Z4 "inertia two-cell component hom-lift"]
theorem component.isHomLift (η : F ⟶ G) (A : (inertia X).obj) :
    (inertia Y).p.IsHomLift (𝟙 ((inertia X).p.obj A)) (component η A) := sorry

end map₂

/-- A based `2`-morphism induces a based `2`-morphism between the corresponding inertia
maps. -/
@[stacks 04Z4 "based inertia action on 2-morphisms"]
def map₂ (η : F ⟶ G) : map F ⟶ map G where
  toNatTrans :=
    { app := map₂.component η
      naturality := fun {_ _} φ ↦ map₂.component.naturality η φ }
  isHomLift' := map₂.component.isHomLift η

namespace map₂

/-- Based inertia preserves identity `2`-morphisms. -/
@[simp, stacks 04Z4 "based inertia two-cell identity"]
theorem id (F : X ⥤ᵇ Y) :
    map₂ (𝟙 F) = 𝟙 (map F) := sorry

/-- Based inertia preserves vertical composition of `2`-morphisms. -/
@[simp, stacks 04Z4 "based inertia two-cell composition"]
theorem comp (η : F ⟶ G) (θ : G ⟶ H) :
    map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := sorry

end map₂

/-- Inertia acts functorially on each hom category of based categories over `C`. -/
@[stacks 04Z4 "based inertia local hom functor"]
def mapFunctor
    (X : BasedCategory.{v₁, u₁} C)
    (Y : BasedCategory.{v₂, u₂} C) :
    (X ⥤ᵇ Y) ⥤ (inertia X ⥤ᵇ inertia Y) where
  obj := map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

/-- A based natural isomorphism induces an isomorphism between the corresponding inertia
maps. -/
@[stacks 04Z4 "based inertia map isomorphism"]
def mapIso (e : F ≅ G) : map F ≅ map G :=
  (mapFunctor X Y).mapIso e

end Inertia

end BasedCategory
end CategoryTheory
