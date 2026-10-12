/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Computations.Naturality
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.Tactic.CrossRefAttribute

/-!
# The forgetful strong transformation for ordinary inertia

In a universe stable under the inertia construction, the forgetful functors form a
strong transformation from the inertia pseudofunctor to the identity pseudofunctor.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

universe u v w

namespace CategoryTheory.Inertia

namespace pseudofunctor.forget

variable {C D : Cat.{v, max w v}}

/-- The objectwise component of forgetful naturality is the identity isomorphism. -/
@[stacks 042H "inertia forgetful strong-transformation component"]
def component (F : C ⟶ D) (X : Inertia C) :
    ((CategoryTheory.Inertia.pseudofunctor).map F ≫
        (CategoryTheory.Inertia.forget D).toCatHom).toFunctor.obj X ≅
      ((CategoryTheory.Inertia.forget C).toCatHom ≫ F).toFunctor.obj X :=
  Iso.refl _

/-- Naturality of the objectwise forgetful components. -/
@[stacks 042H "inertia forgetful strong-transformation component naturality"]
theorem component.naturality (F : C ⟶ D)
    {X Y : Inertia C} (f : X ⟶ Y) :
    ((CategoryTheory.Inertia.pseudofunctor).map F ≫
        (CategoryTheory.Inertia.forget D).toCatHom).toFunctor.map f ≫
        (component F Y).hom =
      (component F X).hom ≫
        ((CategoryTheory.Inertia.forget C).toCatHom ≫ F).toFunctor.map f := sorry

/-- The identity components form a natural isomorphism for forgetting inertia. -/
@[stacks 042H "inertia forgetful strong-transformation naturality"]
def naturalityIso (F : C ⟶ D) :
    (CategoryTheory.Inertia.pseudofunctor).map F ≫
        (CategoryTheory.Inertia.forget D).toCatHom ≅
      (CategoryTheory.Inertia.forget C).toCatHom ≫ F :=
  Cat.Hom.isoMk <| NatIso.ofComponents
    (component F)
    (component.naturality F)

namespace Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Naturality of the forgetful strong transformation on `2`-cells. -/
private theorem naturality_naturality
    {C D : Cat.{v, max w v}} {F G : C ⟶ D} (η : F ⟶ G) :
    (CategoryTheory.Inertia.pseudofunctor).map₂ η ▷
        (CategoryTheory.Inertia.forget D).toCatHom ≫
        (naturalityIso G).hom =
      (naturalityIso F).hom ≫
        (CategoryTheory.Inertia.forget C).toCatHom ◁
          (Pseudofunctor.id (Cat.{v, max w v})).map₂ η := sorry

/-- Identity coherence for the forgetful strong transformation. -/
private theorem naturality_id (C : Cat.{v, max w v}) :
    (naturalityIso (𝟙 C)).hom ≫
        (CategoryTheory.Inertia.forget C).toCatHom ◁
          ((Pseudofunctor.id (Cat.{v, max w v})).mapId C).hom =
      ((CategoryTheory.Inertia.pseudofunctor).mapId C).hom ▷
          (CategoryTheory.Inertia.forget C).toCatHom ≫
        (λ_ ((CategoryTheory.Inertia.forget C).toCatHom)).hom ≫
        (ρ_ ((CategoryTheory.Inertia.forget C).toCatHom)).inv := sorry

/-- Composition coherence for the forgetful strong transformation. -/
private theorem naturality_comp
    {C D E : Cat.{v, max w v}} (F : C ⟶ D) (G : D ⟶ E) :
    (naturalityIso (F ≫ G)).hom ≫
        (CategoryTheory.Inertia.forget C).toCatHom ◁
          ((Pseudofunctor.id (Cat.{v, max w v})).mapComp F G).hom =
      ((CategoryTheory.Inertia.pseudofunctor).mapComp F G).hom ▷
          (CategoryTheory.Inertia.forget E).toCatHom ≫
        (α_ _ _ _).hom ≫
        (CategoryTheory.Inertia.pseudofunctor).map F ◁ (naturalityIso G).hom ≫
        (α_ _ _ _).inv ≫
        (naturalityIso F).hom ▷
          (Pseudofunctor.id (Cat.{v, max w v})).map G ≫
        (α_ _ _ _).hom := sorry

end Implementation

/- The component and coherence fields are explicit data/proof owners; only the
coherence side remains deferred at the statement stage. -/
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Forgetting the selected automorphism is a stable-universe strong transformation. -/
@[stacks 042H "inertia forgetful strong-transformation"]
def strongTrans :
    Pseudofunctor.StrongTrans
      ((CategoryTheory.Inertia.pseudofunctor :
        Pseudofunctor (Cat.{v, max w v}) (Cat.{v, max w v})))
      (Pseudofunctor.id (Cat.{v, max w v})) where
  app X := (CategoryTheory.Inertia.forget X).toCatHom
  naturality F := naturalityIso F
  naturality_naturality := Implementation.naturality_naturality
  naturality_id := Implementation.naturality_id
  naturality_comp := Implementation.naturality_comp

namespace strongTrans

/-- The component of the forgetful strong transformation is the canonical forgetful functor. -/
@[simp, stacks 042H "inertia forgetful strong-transformation object"]
theorem app (X : Cat.{v, max w v}) :
    (CategoryTheory.Inertia.pseudofunctor.forget.strongTrans).app X =
      (CategoryTheory.Inertia.forget X).toCatHom := sorry

/-- The naturality cell of the forgetful strong transformation is the canonical comparison. -/
@[simp, stacks 042H "inertia forgetful strong-transformation naturality readout"]
theorem naturality {X Y : Cat.{v, max w v}} (F : X ⟶ Y) :
    (CategoryTheory.Inertia.pseudofunctor.forget.strongTrans).naturality F =
      CategoryTheory.Inertia.pseudofunctor.forget.naturalityIso F := sorry

end strongTrans

end pseudofunctor.forget

end CategoryTheory.Inertia
