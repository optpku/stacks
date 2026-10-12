/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Computations for full-subbicategory pseudofunctor lifts

This module exposes the object, `1`-cell, `2`-cell, comparison, and
factorization computations of the canonical arbitrary pseudofunctor lift.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u' w' v'

namespace ObjectProperty

variable {D : Type u} [Bicategory.{w, v} D]

namespace FullSubbicategory

variable {P : ObjectProperty D}

section PseudofunctorLift

variable {A : Type u'} [Bicategory.{w', v'} A]

/-- A lifted pseudofunctor sends an object to its ambient image equipped with
the supplied membership witness. -/
@[simp]
theorem liftPseudofunctor.obj (G : Pseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    (X : A) :
    (liftPseudofunctor G obj_mem).obj X = mk P (G.obj X) (obj_mem X) := sorry

/-- Forgetting the object-property witness after applying a lifted
pseudofunctor to a `1`-morphism recovers the original ambient image. -/
@[simp]
theorem liftPseudofunctor.map (G : Pseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} (f : X ⟶ Y) :
    ((liftPseudofunctor G obj_mem).map f).hom = G.map f := sorry

/-- Forgetting the object-property witness after applying a lifted
pseudofunctor to a `2`-morphism recovers the original ambient image. -/
@[simp]
theorem liftPseudofunctor.map₂ (G : Pseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} {f g : X ⟶ Y} (η : f ⟶ g) :
    ((liftPseudofunctor G obj_mem).map₂ η).hom = G.map₂ η := sorry

/-- The forward identity comparison of a pseudofunctor lift has the original
ambient forward identity comparison. -/
@[simp]
theorem liftPseudofunctor.mapId.hom.toAmbient
    (G : Pseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X)) (X : A) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((liftPseudofunctor G obj_mem).mapId X)).hom = (G.mapId X).hom := sorry

/-- The inverse identity comparison of a pseudofunctor lift has the original
ambient inverse identity comparison. -/
@[simp]
theorem liftPseudofunctor.mapId.inv.toAmbient
    (G : Pseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X)) (X : A) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((liftPseudofunctor G obj_mem).mapId X)).inv = (G.mapId X).inv := sorry

/-- The forward composition comparison of a pseudofunctor lift has the
original ambient forward composition comparison. -/
@[simp]
theorem liftPseudofunctor.mapComp.hom.toAmbient
    (G : Pseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((liftPseudofunctor G obj_mem).mapComp f g)).hom = (G.mapComp f g).hom := sorry

/-- The inverse composition comparison of a pseudofunctor lift has the
original ambient inverse composition comparison. -/
@[simp]
theorem liftPseudofunctor.mapComp.inv.toAmbient
    (G : Pseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((liftPseudofunctor G obj_mem).mapComp f g)).inv = (G.mapComp f g).inv := sorry

/-- Composing a pseudofunctor lift with the full-subbicategory inclusion
forgets exactly the added object-membership witnesses. -/
theorem liftPseudofunctor.comp_ι
    (G : Pseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X)) :
    (liftPseudofunctor G obj_mem).comp (ι P).toPseudofunctor = G := sorry

end PseudofunctorLift

end FullSubbicategory

end ObjectProperty

end CategoryTheory
