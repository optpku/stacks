/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudofunctor lifts to full subbicategories

An arbitrary pseudofunctor whose image objects satisfy an object property
factors canonically through the associated full subbicategory.  This file
contains only the construction; its computation and factorization lemmas live
in `FullSubbicategory.Pseudofunctor.Computations`.
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

namespace Implementation

/-- The object, morphism, and `2`-morphism data of the pseudofunctor lift. -/
private def prelaxStruct (G : Pseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X)) :
    PrelaxFunctorStruct A P.FullSubbicategory where
  obj := fun X ↦ mk P (G.obj X) (obj_mem X)
  map := fun f ↦ Bicategory.InducedBicategory.mkHom (G.map f)
  map₂ := fun eta ↦ Bicategory.InducedBicategory.mkHom₂ (G.map₂ eta)

/-- The lifted `2`-morphism action preserves identities. -/
private theorem map₂Id (G : Pseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} (f : X ⟶ Y) :
    (prelaxStruct G obj_mem).map₂ (𝟙 f) =
      𝟙 ((prelaxStruct G obj_mem).map f) := sorry

/-- The lifted `2`-morphism action preserves vertical composition. -/
private theorem map₂Comp (G : Pseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} {f g h : X ⟶ Y} (eta : f ⟶ g) (theta : g ⟶ h) :
    (prelaxStruct G obj_mem).map₂ (eta ≫ theta) =
      (prelaxStruct G obj_mem).map₂ eta ≫
        (prelaxStruct G obj_mem).map₂ theta := sorry

/-- The prelax functor underlying the pseudofunctor lift. -/
private def prelax (G : Pseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X)) :
    PrelaxFunctor A P.FullSubbicategory where
  toPrelaxFunctorStruct := prelaxStruct G obj_mem
  map₂_id := map₂Id G obj_mem
  map₂_comp := map₂Comp G obj_mem

/-- The identity comparison of the pseudofunctor lift. -/
private def mapId (G : Pseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X)) (X : A) :
    (prelax G obj_mem).map (𝟙 X) ≅ 𝟙 ((prelax G obj_mem).obj X) :=
  Bicategory.InducedBicategory.isoMk (G.mapId X)

/-- The composition comparison of the pseudofunctor lift. -/
private def mapComp (G : Pseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (prelax G obj_mem).map (f ≫ g) ≅
      (prelax G obj_mem).map f ≫ (prelax G obj_mem).map g :=
  Bicategory.InducedBicategory.isoMk (G.mapComp f g)

/-- Left-whiskering coherence for the pseudofunctor lift. -/
private theorem map₂WhiskerLeft (G : Pseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    {X Y Z : A} (f : X ⟶ Y) {g h : Y ⟶ Z} (eta : g ⟶ h) :
    (prelax G obj_mem).map₂ (f ◁ eta) =
      (mapComp G obj_mem f g).hom ≫
        (prelax G obj_mem).map f ◁ (prelax G obj_mem).map₂ eta ≫
          (mapComp G obj_mem f h).inv := sorry

/-- Right-whiskering coherence for the pseudofunctor lift. -/
private theorem map₂WhiskerRight (G : Pseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    {X Y Z : A} {f g : X ⟶ Y} (eta : f ⟶ g) (h : Y ⟶ Z) :
    (prelax G obj_mem).map₂ (eta ▷ h) =
      (mapComp G obj_mem f h).hom ≫
        (prelax G obj_mem).map₂ eta ▷ (prelax G obj_mem).map h ≫
          (mapComp G obj_mem g h).inv := sorry

/-- Associator coherence for the pseudofunctor lift. -/
private theorem map₂Associator (G : Pseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (prelax G obj_mem).map₂ (α_ f g h).hom =
      (mapComp G obj_mem (f ≫ g) h).hom ≫
        (mapComp G obj_mem f g).hom ▷ (prelax G obj_mem).map h ≫
          (α_ ((prelax G obj_mem).map f) ((prelax G obj_mem).map g)
            ((prelax G obj_mem).map h)).hom ≫
            (prelax G obj_mem).map f ◁ (mapComp G obj_mem g h).inv ≫
              (mapComp G obj_mem f (g ≫ h)).inv := sorry

/-- Left-unitor coherence for the pseudofunctor lift. -/
private theorem map₂LeftUnitor (G : Pseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} (f : X ⟶ Y) :
    (prelax G obj_mem).map₂ (λ_ f).hom =
      (mapComp G obj_mem (𝟙 X) f).hom ≫
        (mapId G obj_mem X).hom ▷ (prelax G obj_mem).map f ≫
          (λ_ ((prelax G obj_mem).map f)).hom := sorry

/-- Right-unitor coherence for the pseudofunctor lift. -/
private theorem map₂RightUnitor (G : Pseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} (f : X ⟶ Y) :
    (prelax G obj_mem).map₂ (ρ_ f).hom =
      (mapComp G obj_mem f (𝟙 Y)).hom ≫
        (prelax G obj_mem).map f ◁ (mapId G obj_mem Y).hom ≫
          (ρ_ ((prelax G obj_mem).map f)).hom := sorry

end Implementation

/-- Lift a pseudofunctor to the full subbicategory selected by `P` when every
image object satisfies `P`.

The lift retains the object, `1`-morphism, `2`-morphism, identity-comparison,
and composition-comparison data of the original pseudofunctor; it only adds
the specified object-membership witnesses. -/
def liftPseudofunctor (G : Pseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X)) :
    Pseudofunctor A P.FullSubbicategory where
  toPrelaxFunctor := Implementation.prelax G obj_mem
  mapId := Implementation.mapId G obj_mem
  mapComp := Implementation.mapComp G obj_mem
  map₂_whisker_left := Implementation.map₂WhiskerLeft G obj_mem
  map₂_whisker_right := Implementation.map₂WhiskerRight G obj_mem
  map₂_associator := Implementation.map₂Associator G obj_mem
  map₂_left_unitor := Implementation.map₂LeftUnitor G obj_mem
  map₂_right_unitor := Implementation.map₂RightUnitor G obj_mem

end PseudofunctorLift

end FullSubbicategory

end ObjectProperty

end CategoryTheory
