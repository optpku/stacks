/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Computations.Naturality
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.Tactic.CrossRefAttribute

/-!
# The identity-section strong transformation for ordinary inertia

In a stable universe, the identity-automorphism section is a strong transformation
from the identity pseudofunctor to ordinary inertia.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

universe u v w

namespace CategoryTheory.Inertia

namespace pseudofunctor.identitySection

variable {C D : Cat.{v, max w v}}

/-- The identity arrow intertwines the automorphisms in identity-section naturality. -/
theorem component.comm (F : C ⟶ D) (X : C) :
    (((Pseudofunctor.id (Cat.{v, max w v})).map F ≫
        (CategoryTheory.Inertia.identitySection D).toCatHom).toFunctor.obj X).aut.hom ≫
        𝟙 _ =
      𝟙 _ ≫
        (((CategoryTheory.Inertia.identitySection C).toCatHom ≫
          (CategoryTheory.Inertia.pseudofunctor).map F).toFunctor.obj X).aut.hom := sorry

/-- The objectwise component of identity-section naturality is the identity isomorphism. -/
@[stacks 04Z3 "inertia identity-section strong-transformation component"]
def component (F : C ⟶ D) (X : C) :
    ((Pseudofunctor.id (Cat.{v, max w v})).map F ≫
        (CategoryTheory.Inertia.identitySection D).toCatHom).toFunctor.obj X ≅
    ((CategoryTheory.Inertia.identitySection C).toCatHom ≫
        (CategoryTheory.Inertia.pseudofunctor).map F).toFunctor.obj X :=
  CategoryTheory.Inertia.isoMk (Iso.refl _) (component.comm F X)

/-- Naturality of the objectwise identity-section components. -/
theorem component.naturality (F : C ⟶ D)
    {X Y : C} (f : X ⟶ Y) :
    ((Pseudofunctor.id (Cat.{v, max w v})).map F ≫
        (CategoryTheory.Inertia.identitySection D).toCatHom).toFunctor.map f ≫
        (component F Y).hom =
      (component F X).hom ≫
        ((CategoryTheory.Inertia.identitySection C).toCatHom ≫
          (CategoryTheory.Inertia.pseudofunctor).map F).toFunctor.map f := sorry

/-- The identity components form a natural isomorphism for the identity section. -/
@[stacks 04Z3 "inertia identity-section strong-transformation naturality"]
def naturalityIso (F : C ⟶ D) :
    (Pseudofunctor.id (Cat.{v, max w v})).map F ≫
        (CategoryTheory.Inertia.identitySection D).toCatHom ≅
      (CategoryTheory.Inertia.identitySection C).toCatHom ≫
        (CategoryTheory.Inertia.pseudofunctor).map F :=
  Cat.Hom.isoMk <| NatIso.ofComponents
    (component F)
    (component.naturality F)

namespace Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Naturality of the identity-section strong transformation on `2`-cells. -/
private theorem naturality_naturality
    {C D : Cat.{v, max w v}} {F G : C ⟶ D} (η : F ⟶ G) :
    (Pseudofunctor.id (Cat.{v, max w v})).map₂ η ▷
        (CategoryTheory.Inertia.identitySection D).toCatHom ≫
        (naturalityIso G).hom =
      (naturalityIso F).hom ≫
        (CategoryTheory.Inertia.identitySection C).toCatHom ◁
          (CategoryTheory.Inertia.pseudofunctor).map₂ η := sorry

/-- Identity coherence for the identity-section strong transformation. -/
private theorem naturality_id (C : Cat.{v, max w v}) :
    (naturalityIso (𝟙 C)).hom ≫
        (CategoryTheory.Inertia.identitySection C).toCatHom ◁
          ((CategoryTheory.Inertia.pseudofunctor).mapId C).hom =
      ((Pseudofunctor.id (Cat.{v, max w v})).mapId C).hom ▷
          (CategoryTheory.Inertia.identitySection C).toCatHom ≫
        (λ_ ((CategoryTheory.Inertia.identitySection C).toCatHom)).hom ≫
        (ρ_ ((CategoryTheory.Inertia.identitySection C).toCatHom)).inv := sorry

/-- Composition coherence for the identity-section strong transformation. -/
private theorem naturality_comp
    {C D E : Cat.{v, max w v}} (F : C ⟶ D) (G : D ⟶ E) :
    (naturalityIso (F ≫ G)).hom ≫
        (CategoryTheory.Inertia.identitySection C).toCatHom ◁
          ((CategoryTheory.Inertia.pseudofunctor).mapComp F G).hom =
      ((Pseudofunctor.id (Cat.{v, max w v})).mapComp F G).hom ▷
          (CategoryTheory.Inertia.identitySection E).toCatHom ≫
        (α_ _ _ _).hom ≫
        (Pseudofunctor.id (Cat.{v, max w v})).map F ◁
          (naturalityIso G).hom ≫
        (α_ _ _ _).inv ≫
        (naturalityIso F).hom ▷
          (CategoryTheory.Inertia.pseudofunctor).map G ≫
        (α_ _ _ _).hom := sorry

end Implementation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Inserting the identity automorphism is a stable-universe strong transformation. -/
@[stacks 04Z3 "inertia identity-section strong-transformation"]
def strongTrans :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.id (Cat.{v, max w v}))
      ((CategoryTheory.Inertia.pseudofunctor :
        Pseudofunctor (Cat.{v, max w v}) (Cat.{v, max w v}))) where
  app X := (CategoryTheory.Inertia.identitySection X).toCatHom
  naturality F := naturalityIso F
  naturality_naturality := Implementation.naturality_naturality
  naturality_id := Implementation.naturality_id
  naturality_comp := Implementation.naturality_comp

namespace strongTrans

/-- The component of the identity-section strong transformation is the canonical section. -/
@[simp, stacks 04Z3 "inertia identity-section strong-transformation object"]
theorem app (X : Cat.{v, max w v}) :
    (CategoryTheory.Inertia.pseudofunctor.identitySection.strongTrans).app X =
      (CategoryTheory.Inertia.identitySection X).toCatHom := sorry

/-- The naturality cell of the identity-section strong transformation is the canonical comparison. -/
@[simp, stacks 04Z3 "inertia identity-section strong-transformation naturality readout"]
theorem naturality {X Y : Cat.{v, max w v}} (F : X ⟶ Y) :
    (CategoryTheory.Inertia.pseudofunctor.identitySection.strongTrans).naturality F =
      CategoryTheory.Inertia.pseudofunctor.identitySection.naturalityIso F := sorry

end strongTrans

end pseudofunctor.identitySection

end CategoryTheory.Inertia
