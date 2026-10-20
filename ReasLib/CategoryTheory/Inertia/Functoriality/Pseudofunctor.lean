/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import ReasLib.CategoryTheory.Inertia.Functoriality.NatTrans
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict-pseudofunctor owner for inertia

This module contains the concrete Cat-level data owner. The public projection and computation
API is split into sibling modules so consumers can depend only on the layer they use.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v

namespace CategoryTheory
namespace Inertia

section PseudofunctorImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The bundled inertia category attached to an object of Cat. -/
private def objOwner (C : Cat.{v, u}) : Cat.{v, max u v} :=
  Cat.of (Inertia C)

/-- The bundled inertia functor attached to a 1-morphism of Cat. -/
private def mapOwner {C D : Cat.{v, u}} (F : C ⟶ D) :
    objOwner C ⟶ objOwner D :=
  (Inertia.map F.toFunctor).toCatHom

/-- The bundled inertia transformation attached to a 2-morphism of Cat. -/
private def map₂Owner {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) :
    mapOwner F ⟶ mapOwner G :=
  (Inertia.map₂ η.toNatTrans).toCatHom₂

/-- The bundled inertia action preserves identity 2-morphisms. -/
private theorem map₂Owner_id {C D : Cat.{v, u}} (F : C ⟶ D) :
    map₂Owner (𝟙 F) = 𝟙 (mapOwner F) := sorry

/-- The bundled inertia action preserves vertical composition of 2-morphisms. -/
private theorem map₂Owner_comp {C D : Cat.{v, u}} {F G H : C ⟶ D}
    (η : F ⟶ G) (θ : G ⟶ H) :
    map₂Owner (η ≫ θ) = map₂Owner η ≫ map₂Owner θ := sorry

/-- The functor induced by inertia on a hom category of Cat. This is the bundled
counterpart of Inertia.mapFunctor and is the locally functorial part of the inertia
pseudofunctor. -/
@[stacks 04Z4 "bundled inertia local hom functor"]
def catHomFunctor (C D : Cat.{v, u}) :
    (C ⟶ D) ⥤
      ((Cat.of (Inertia C)) ⟶ (Cat.of (Inertia D))) where
  obj := mapOwner
  map := map₂Owner
  map_id := map₂Owner_id
  map_comp := map₂Owner_comp

/-- The bundled inertia action preserves identity 1-morphisms strictly. -/
private theorem mapOwner_id (C : Cat.{v, u}) :
    mapOwner (𝟙 C) = 𝟙 (objOwner C) := sorry

/-- The bundled inertia action preserves horizontal composition strictly. -/
private theorem mapOwner_comp {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) :
    mapOwner (F ≫ G) = mapOwner F ≫ mapOwner G := sorry

/-- The bundled inertia action is compatible with left whiskering. -/
private theorem map₂Owner_whisker_left
    {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) :
    map₂Owner (F ◁ η) =
      eqToHom (mapOwner_comp F G) ≫
        mapOwner F ◁ map₂Owner η ≫
          eqToHom (mapOwner_comp F H).symm := sorry

/-- The bundled inertia action is compatible with right whiskering. -/
private theorem map₂Owner_whisker_right
    {C D E : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) (H : D ⟶ E) :
    map₂Owner (η ▷ H) =
      eqToHom (mapOwner_comp F H) ≫
        map₂Owner η ▷ mapOwner H ≫
          eqToHom (mapOwner_comp G H).symm := sorry

/-- The explicit strict-pseudofunctor pre-core of the inertia construction. -/
private def preCore :
    StrictPseudofunctorPreCore Cat.{v, u} Cat.{v, max u v} where
  __ := PrelaxFunctor.mkOfHomFunctors objOwner catHomFunctor
  map_id := mapOwner_id
  map_comp := mapOwner_comp
  map₂_whisker_left := map₂Owner_whisker_left
  map₂_whisker_right := map₂Owner_whisker_right

/-- Inertia is a strict pseudofunctor on the bicategory of categories. Its 2-cell action
sends η : F ⟶ G to the intertwiner with component η.app X.obj at (X.obj, X.aut). Since Cat
is a strict bicategory, StrictPseudofunctor.mk'' supplies the associator and unitor coherence
from preCore. -/
@[stacks 04Z4 "strict pseudofunctorial abstract inertia"]
def strictPseudofunctor :
    StrictPseudofunctor Cat.{v, u} Cat.{v, max u v} :=
  StrictPseudofunctor.mk'' preCore

/-- The pseudofunctor view of the strict inertia pseudofunctor. This is the convenient
interface for APIs stated for arbitrary pseudofunctors. -/
@[stacks 04Z4 "pseudofunctorial abstract inertia"]
def pseudofunctor :
    Pseudofunctor Cat.{v, u} Cat.{v, max u v} :=
  strictPseudofunctor.toPseudofunctor

end PseudofunctorImplementation

/-- The underlying pseudofunctor of the strict inertia pseudofunctor is the standard
pseudofunctor view. -/
@[simp, stacks 04Z4 "strict inertia pseudofunctor projection"]
theorem strictPseudofunctor.toPseudofunctor :
    strictPseudofunctor.toPseudofunctor = pseudofunctor := sorry

end Inertia
end CategoryTheory
