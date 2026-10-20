/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Widesubcategory
public import ReasLib.RingTheory.RingHom.Local.Map

/-!
# Local algebra object and morphism properties

This module defines the object property of local algebras and the morphism property of local
algebra homomorphisms.
-/

@[expose] public section

open CategoryTheory

universe u v

variable (A : Type u) [CommRing A]

/-- The property that an `A`-algebra is local and that its structure map is local. -/
def LocalAlgCat.objectProperty : ObjectProperty (CommAlgCat.{v} A) :=
  fun T ↦ IsLocalRing T ∧ IsLocalHom (algebraMap A T)

/-- Membership in `objectProperty A` is exactly locality of the target and its structure map. -/
theorem LocalAlgCat.objectProperty_iff (T : CommAlgCat.{v} A) :
    LocalAlgCat.objectProperty A T ↔ IsLocalRing T ∧ IsLocalHom (algebraMap A T) := sorry

/-- The property that a morphism between local `A`-algebras is a local ring homomorphism. -/
def LocalAlgCat.morphismProperty :
    MorphismProperty (LocalAlgCat.objectProperty.{u, v} A).FullSubcategory :=
  fun _ _ f ↦ IsLocalHom f.hom.hom.toRingHom

/-- Membership in `morphismProperty A` is exactly locality of the underlying ring map. -/
theorem LocalAlgCat.morphismProperty_iff
    {T U : (LocalAlgCat.objectProperty.{u, v} A).FullSubcategory}
    (f : T ⟶ U) :
    LocalAlgCat.morphismProperty A f ↔ IsLocalHom f.hom.hom.toRingHom := sorry

/-- Local algebra morphisms contain identities and are closed under composition. -/
instance LocalAlgCat.morphismPropertyIsMultiplicative :
    (LocalAlgCat.morphismProperty.{u, v} A).IsMultiplicative := sorry
