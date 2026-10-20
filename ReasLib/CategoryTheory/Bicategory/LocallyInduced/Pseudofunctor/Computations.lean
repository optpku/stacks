/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Iso
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Computations for locally induced pseudofunctor lifts

This module exposes the object, `1`-cell, `2`-cell, and comparison actions of
the canonical arbitrary pseudofunctor lift.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u' w' v' u''

namespace Bicategory

variable {B : Type u'}

namespace LocallyInducedBicategory

variable {C : Type u} [Bicategory.{w, v} C] {F : B → C}
  {Q : HomProperty F} [Q.IsMultiplicative]

section PseudofunctorLift

variable {A : Type u''} [Bicategory.{w', v'} A]

/-- A pseudofunctor lift retains the object action of the original
pseudofunctor. -/
@[simp]
theorem liftPseudofunctor.obj (G : Pseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom) (X : A) :
    (liftPseudofunctor G map_mem).obj X = G.obj X := sorry

/-- The ambient representative of the image of a `1`-morphism under a
pseudofunctor lift is its original ambient image. -/
@[simp]
theorem liftPseudofunctor.map.toAmbient
    (G : Pseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y : A} (f : X ⟶ Y) :
    ((liftPseudofunctor G map_mem).map f).obj =
      (G.map f).hom := sorry

/-- The ambient representative of the image of a `2`-morphism under a
pseudofunctor lift is its original ambient cell. -/
@[simp]
theorem liftPseudofunctor.map₂.toAmbient
    (G : Pseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y : A} {f g : X ⟶ Y} (η : f ⟶ g) :
    ((liftPseudofunctor G map_mem).map₂ η).hom =
      (G.map₂ η).hom := sorry

/-- The ambient forward identity comparison of a pseudofunctor lift is the
corresponding comparison of the original pseudofunctor. -/
@[simp]
theorem liftPseudofunctor.mapId.hom.toAmbient
    (G : Pseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom) (X : A) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((liftPseudofunctor G map_mem).mapId X)).hom =
      (InducedBicategory.Iso.toAmbient (G.mapId X)).hom := sorry

/-- The ambient inverse identity comparison of a pseudofunctor lift is the
corresponding comparison of the original pseudofunctor. -/
@[simp]
theorem liftPseudofunctor.mapId.inv.toAmbient
    (G : Pseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom) (X : A) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((liftPseudofunctor G map_mem).mapId X)).inv =
      (InducedBicategory.Iso.toAmbient (G.mapId X)).inv := sorry

/-- The ambient forward composition comparison of a pseudofunctor lift is the
corresponding comparison of the original pseudofunctor. -/
@[simp]
theorem liftPseudofunctor.mapComp.hom.toAmbient
    (G : Pseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((liftPseudofunctor G map_mem).mapComp f g)).hom =
      (InducedBicategory.Iso.toAmbient (G.mapComp f g)).hom := sorry

/-- The ambient inverse composition comparison of a pseudofunctor lift is the
corresponding comparison of the original pseudofunctor. -/
@[simp]
theorem liftPseudofunctor.mapComp.inv.toAmbient
    (G : Pseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((liftPseudofunctor G map_mem).mapComp f g)).inv =
      (InducedBicategory.Iso.toAmbient (G.mapComp f g)).inv := sorry

end PseudofunctorLift

end LocallyInducedBicategory

end Bicategory

end CategoryTheory
