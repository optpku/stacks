/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Strong transformations between strict full-subbicategory lifts

This leaf lifts strong transformations between ambient strict pseudofunctors and provides the
specializations whose other endpoint is the canonical full-subbicategory inclusion.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty.FullSubbicategory

open CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory

variable {D : Type u} [Bicategory.{w, v} D]
variable {P : ObjectProperty D}

namespace StrongTrans

section Lift

universe wA vA uA

variable {A : Type uA} [Bicategory.{wA, vA} A]

namespace Lift

variable (F G : StrictPseudofunctor A D)
variable (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)

/-- A component of an ambient strong transformation, regarded in the selected full
subbicategory. -/
def app (X : A) :
    (FullSubbicategory.lift F hF).obj X ⟶
      (FullSubbicategory.lift G hG).obj X :=
  Bicategory.InducedBicategory.mkHom (η.app X)

/-- An ambient naturality isomorphism, regarded in the selected full subbicategory. -/
def naturality {X Y : A} (f : X ⟶ Y) :
    (FullSubbicategory.lift F hF).map f ≫ app F G hF hG η Y ≅
      app F G hF hG η X ≫ (FullSubbicategory.lift G hG).map f :=
  Bicategory.InducedBicategory.isoMk (η.naturality f)

/-- Naturality in source `2`-cells for a lifted strong transformation. -/
theorem naturality_naturality :
    ∀ {X Y : A} {f g : X ⟶ Y} (τ : f ⟶ g),
      (FullSubbicategory.lift F hF).map₂ τ ▷ app F G hF hG η Y ≫
          (naturality F G hF hG η g).hom =
        (naturality F G hF hG η f).hom ≫
          app F G hF hG η X ◁ (FullSubbicategory.lift G hG).map₂ τ := by
  intro X Y f g τ
  apply Bicategory.InducedBicategory.hom₂_ext
  exact η.naturality_naturality τ

/-- Identity coherence for a lifted strong transformation. -/
theorem naturality_id :
    ∀ X : A,
      (naturality F G hF hG η (𝟙 X)).hom ≫
          app F G hF hG η X ◁ ((FullSubbicategory.lift G hG).mapId X).hom =
        ((FullSubbicategory.lift F hF).mapId X).hom ▷ app F G hF hG η X ≫
          (λ_ (app F G hF hG η X)).hom ≫
          (ρ_ (app F G hF hG η X)).inv := by
  intro X
  apply Bicategory.InducedBicategory.hom₂_ext
  change (η.naturality (𝟙 X)).hom ≫
      η.app X ◁ ((FullSubbicategory.lift G hG).mapId X).hom.hom =
    ((FullSubbicategory.lift F hF).mapId X).hom.hom ▷ η.app X ≫
      (λ_ (η.app X)).hom ≫ (ρ_ (η.app X)).inv
  set_option backward.isDefEq.respectTransparency false in
    simpa only [StrictlyUnitaryPseudofunctor.mapId_eq_eqToIso, eqToIso.hom,
      Bicategory.InducedBicategory.eqToHom_hom] using η.naturality_id X

/-- Composition coherence for a lifted strong transformation. -/
theorem naturality_comp :
    ∀ {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z),
      (naturality F G hF hG η (f ≫ g)).hom ≫
          app F G hF hG η X ◁ ((FullSubbicategory.lift G hG).mapComp f g).hom =
        ((FullSubbicategory.lift F hF).mapComp f g).hom ▷
            app F G hF hG η Z ≫
          (α_ _ _ _).hom ≫
          (FullSubbicategory.lift F hF).map f ◁
            (naturality F G hF hG η g).hom ≫
          (α_ _ _ _).inv ≫
          (naturality F G hF hG η f).hom ▷
            (FullSubbicategory.lift G hG).map g ≫
          (α_ _ _ _).hom := by
  intro X Y Z f g
  apply Bicategory.InducedBicategory.hom₂_ext
  change (η.naturality (f ≫ g)).hom ≫
      η.app X ◁ ((FullSubbicategory.lift G hG).mapComp f g).hom.hom =
    ((FullSubbicategory.lift F hF).mapComp f g).hom.hom ▷ η.app Z ≫
      (α_ _ _ _).hom ≫ F.map f ◁ (η.naturality g).hom ≫
      (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom
  have h := η.naturality_comp f g
  simp only [StrictPseudofunctor.mapComp_eq_eqToIso, eqToIso.hom] at h
  simp only [StrictPseudofunctor.mapComp_eq_eqToIso, eqToIso.hom,
    Bicategory.InducedBicategory.eqToHom_hom]
  convert h using 1 <;> rfl

end Lift

/-- Lift a strong transformation between ambient strict pseudofunctors through a
property-selected full subbicategory. Only object-membership witnesses are added. -/
def lift (F G : StrictPseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) :
    Pseudofunctor.StrongTrans (FullSubbicategory.lift F hF).toPseudofunctor
      (FullSubbicategory.lift G hG).toPseudofunctor where
  app := Lift.app F G hF hG η
  naturality := Lift.naturality F G hF hG η
  naturality_naturality := Lift.naturality_naturality F G hF hG η
  naturality_id := Lift.naturality_id F G hF hG η
  naturality_comp := Lift.naturality_comp F G hF hG η

/-- Components of `lift` are the ambient components with object-membership witnesses added. -/
@[simp]
theorem lift.app (F G : StrictPseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) (X : A) :
    (lift F G hF hG η).app X =
      Bicategory.InducedBicategory.mkHom (η.app X) := rfl

/-- Naturality of `lift` is the ambient naturality isomorphism with object-membership
witnesses added. -/
@[simp]
theorem lift.naturality (F G : StrictPseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    {X Y : A} (f : X ⟶ Y) :
    (lift F G hF hG η).naturality f =
      Bicategory.InducedBicategory.isoMk (η.naturality f) := rfl

/-- The ambient component of a lifted strict-pseudofunctor transformation is the original
component. -/
@[simp]
theorem lift.app.toAmbient (F G : StrictPseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) (X : A) :
    ((lift F G hF hG η).app X).hom = η.app X := rfl

/-- The forward ambient naturality cell of a lifted strict-pseudofunctor transformation is the
original forward cell. -/
@[simp]
theorem lift.naturality.hom.toAmbient (F G : StrictPseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    {X Y : A} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((lift F G hF hG η).naturality f)).hom = (η.naturality f).hom := rfl

/-- The inverse ambient naturality cell of a lifted strict-pseudofunctor transformation is the
original inverse cell. -/
@[simp]
theorem lift.naturality.inv.toAmbient (F G : StrictPseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    {X Y : A} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((lift F G hF hG η).naturality f)).inv = (η.naturality f).inv := rfl

end Lift

/-- Lift an ambient strong transformation from a strict pseudofunctor on a selected full
subbicategory to its canonical inclusion. The lifted inclusion is definitionally the identity
pseudofunctor on the full subbicategory. -/
def liftToId
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G.toPseudofunctor
      (FullSubbicategory.ι P).toPseudofunctor) :
    Pseudofunctor.StrongTrans
      (FullSubbicategory.lift G obj_mem).toPseudofunctor
      (Pseudofunctor.id P.FullSubbicategory) :=
  lift G (FullSubbicategory.ι P) obj_mem (fun X ↦ X.property) η

/-- A component of `liftToId` is the ambient component regarded in the selected full
subbicategory. -/
@[simp]
theorem liftToId.app
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G.toPseudofunctor
      (FullSubbicategory.ι P).toPseudofunctor)
    (X : P.FullSubbicategory) :
    (liftToId G obj_mem η).app X =
      Bicategory.InducedBicategory.mkHom (η.app X) := rfl

/-- Naturality of `liftToId` is the ambient naturality isomorphism regarded in the selected
full subbicategory. -/
@[simp]
theorem liftToId.naturality
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G.toPseudofunctor
      (FullSubbicategory.ι P).toPseudofunctor)
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (liftToId G obj_mem η).naturality f =
      Bicategory.InducedBicategory.isoMk (η.naturality f) := rfl

/-- The ambient component of `liftToId` is the original component. -/
@[simp]
theorem liftToId.app.toAmbient
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G.toPseudofunctor
      (FullSubbicategory.ι P).toPseudofunctor)
    (X : P.FullSubbicategory) :
    ((liftToId G obj_mem η).app X).hom = η.app X := rfl

/-- The forward ambient naturality cell of `liftToId` is the original forward cell. -/
@[simp]
theorem liftToId.naturality.hom.toAmbient
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G.toPseudofunctor
      (FullSubbicategory.ι P).toPseudofunctor)
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((liftToId G obj_mem η).naturality f)).hom = (η.naturality f).hom := rfl

/-- The inverse ambient naturality cell of `liftToId` is the original inverse cell. -/
@[simp]
theorem liftToId.naturality.inv.toAmbient
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G.toPseudofunctor
      (FullSubbicategory.ι P).toPseudofunctor)
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((liftToId G obj_mem η).naturality f)).inv = (η.naturality f).inv := rfl

/-- Lift an ambient strong transformation from the canonical inclusion of a selected full
subbicategory to a strict pseudofunctor whose values satisfy the object property. -/
def liftFromId
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans (FullSubbicategory.ι P).toPseudofunctor
      G.toPseudofunctor) :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.id P.FullSubbicategory)
      (FullSubbicategory.lift G obj_mem).toPseudofunctor :=
  lift (FullSubbicategory.ι P) G (fun X ↦ X.property) obj_mem η

/-- A component of `liftFromId` is the ambient component regarded in the selected full
subbicategory. -/
@[simp]
theorem liftFromId.app
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans (FullSubbicategory.ι P).toPseudofunctor
      G.toPseudofunctor)
    (X : P.FullSubbicategory) :
    (liftFromId G obj_mem η).app X =
      Bicategory.InducedBicategory.mkHom (η.app X) := rfl

/-- Naturality of `liftFromId` is the ambient naturality isomorphism regarded in the selected
full subbicategory. -/
@[simp]
theorem liftFromId.naturality
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans (FullSubbicategory.ι P).toPseudofunctor
      G.toPseudofunctor)
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (liftFromId G obj_mem η).naturality f =
      Bicategory.InducedBicategory.isoMk (η.naturality f) := rfl

/-- The ambient component of `liftFromId` is the original component. -/
@[simp]
theorem liftFromId.app.toAmbient
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans (FullSubbicategory.ι P).toPseudofunctor
      G.toPseudofunctor)
    (X : P.FullSubbicategory) :
    ((liftFromId G obj_mem η).app X).hom = η.app X := rfl

/-- The forward ambient naturality cell of `liftFromId` is the original forward cell. -/
@[simp]
theorem liftFromId.naturality.hom.toAmbient
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans (FullSubbicategory.ι P).toPseudofunctor
      G.toPseudofunctor)
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((liftFromId G obj_mem η).naturality f)).hom = (η.naturality f).hom := rfl

/-- The inverse ambient naturality cell of `liftFromId` is the original inverse cell. -/
@[simp]
theorem liftFromId.naturality.inv.toAmbient
    (G : StrictPseudofunctor P.FullSubbicategory D)
    (obj_mem : ∀ X : P.FullSubbicategory, P (G.obj X))
    (η : Pseudofunctor.StrongTrans (FullSubbicategory.ι P).toPseudofunctor
      G.toPseudofunctor)
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((liftFromId G obj_mem η).naturality f)).inv = (η.naturality f).inv := rfl

end StrongTrans

end CategoryTheory.ObjectProperty.FullSubbicategory
