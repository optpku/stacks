module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrongTrans.Lift

/-!
# Full-subbicategory strong transformations to and from identity

This leaf restricts ambient strong transformations between a strict endopseudofunctor and the
identity to the full subbicategory preserved by that endopseudofunctor.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty.FullSubbicategory

open CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory

variable {D : Type u} [Bicategory.{w, v} D]
variable {P : ObjectProperty D}

namespace StrongTrans

namespace ToId

variable (F : StrictPseudofunctor D D) (hF : ∀ X : D, P X → P (F.obj X))
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor (Pseudofunctor.id D))

/-- The component of an ambient transformation to the identity, regarded in the selected full
subbicategory. -/
def app (X : P.FullSubbicategory) :
    (FullSubbicategory.map F hF).obj X ⟶ X :=
  Bicategory.InducedBicategory.mkHom (η.app X.1)

/-- The ambient naturality isomorphism, regarded in the selected full subbicategory. -/
def naturality {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (FullSubbicategory.map F hF).map f ≫ app F hF η Y ≅
      app F hF η X ≫ (Pseudofunctor.id P.FullSubbicategory).map f :=
  Bicategory.InducedBicategory.isoMk (η.naturality f.hom)

/-- Naturality in source `2`-cells for the lifted transformation to the identity. -/
theorem naturality_naturality :
    ∀ {X Y : P.FullSubbicategory} {f g : X ⟶ Y} (τ : f ⟶ g),
      (FullSubbicategory.map F hF).map₂ τ ▷ app F hF η Y ≫
          (naturality F hF η g).hom =
        (naturality F hF η f).hom ≫
          app F hF η X ◁ (Pseudofunctor.id P.FullSubbicategory).map₂ τ := sorry

/-- Identity coherence for the lifted transformation to the identity. -/
theorem naturality_id :
    ∀ X : P.FullSubbicategory,
      (naturality F hF η (𝟙 X)).hom ≫
          app F hF η X ◁ ((Pseudofunctor.id P.FullSubbicategory).mapId X).hom =
        ((FullSubbicategory.map F hF).mapId X).hom ▷ app F hF η X ≫
          (λ_ (app F hF η X)).hom ≫ (ρ_ (app F hF η X)).inv := sorry

/-- Composition coherence for the lifted transformation to the identity. -/
theorem naturality_comp :
    ∀ {X Y Z : P.FullSubbicategory} (f : X ⟶ Y) (g : Y ⟶ Z),
      (naturality F hF η (f ≫ g)).hom ≫
          app F hF η X ◁
            ((Pseudofunctor.id P.FullSubbicategory).mapComp f g).hom =
        ((FullSubbicategory.map F hF).mapComp f g).hom ▷ app F hF η Z ≫
          (α_ _ _ _).hom ≫
          (FullSubbicategory.map F hF).map f ◁ (naturality F hF η g).hom ≫
          (α_ _ _ _).inv ≫
          (naturality F hF η f).hom ▷
            (Pseudofunctor.id P.FullSubbicategory).map g ≫
          (α_ _ _ _).hom := sorry

end ToId

/-- Lift an ambient strong transformation from an endopseudofunctor to the identity through a
property-selected full subbicategory. -/
def toId (F : StrictPseudofunctor D D) (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor (Pseudofunctor.id D)) :
    Pseudofunctor.StrongTrans (FullSubbicategory.map F hF).toPseudofunctor
      (Pseudofunctor.id P.FullSubbicategory) where
  app := ToId.app F hF η
  naturality := ToId.naturality F hF η
  naturality_naturality := ToId.naturality_naturality F hF η
  naturality_id := ToId.naturality_id F hF η
  naturality_comp := ToId.naturality_comp F hF η

/-- The component of `toId` is the ambient component with the full-subbicategory witness added. -/
@[simp]
theorem toId.app (F : StrictPseudofunctor D D) (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor (Pseudofunctor.id D))
    (X : P.FullSubbicategory) :
    (toId F hF η).app X = Bicategory.InducedBicategory.mkHom (η.app X.1) := sorry

/-- The naturality isomorphism of `toId` is the ambient naturality isomorphism. -/
@[simp]
theorem toId.naturality (F : StrictPseudofunctor D D)
    (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor (Pseudofunctor.id D))
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (toId F hF η).naturality f =
      Bicategory.InducedBicategory.isoMk (η.naturality f.hom) := sorry

namespace FromId

variable (F : StrictPseudofunctor D D) (hF : ∀ X : D, P X → P (F.obj X))
variable (η : Pseudofunctor.StrongTrans (Pseudofunctor.id D) F.toPseudofunctor)

/-- The component of an ambient transformation from the identity, regarded in the selected full
subbicategory. -/
def app (X : P.FullSubbicategory) :
    X ⟶ (FullSubbicategory.map F hF).obj X :=
  Bicategory.InducedBicategory.mkHom (η.app X.1)

/-- The ambient naturality isomorphism, regarded in the selected full subbicategory. -/
def naturality {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (Pseudofunctor.id P.FullSubbicategory).map f ≫ app F hF η Y ≅
      app F hF η X ≫ (FullSubbicategory.map F hF).map f :=
  Bicategory.InducedBicategory.isoMk (η.naturality f.hom)

/-- Naturality in source `2`-cells for the lifted transformation from the identity. -/
theorem naturality_naturality :
    ∀ {X Y : P.FullSubbicategory} {f g : X ⟶ Y} (τ : f ⟶ g),
      (Pseudofunctor.id P.FullSubbicategory).map₂ τ ▷ app F hF η Y ≫
          (naturality F hF η g).hom =
        (naturality F hF η f).hom ≫
          app F hF η X ◁ (FullSubbicategory.map F hF).map₂ τ := sorry

/-- Identity coherence for the lifted transformation from the identity. -/
theorem naturality_id :
    ∀ X : P.FullSubbicategory,
      (naturality F hF η (𝟙 X)).hom ≫
          app F hF η X ◁ ((FullSubbicategory.map F hF).mapId X).hom =
        ((Pseudofunctor.id P.FullSubbicategory).mapId X).hom ▷ app F hF η X ≫
          (λ_ (app F hF η X)).hom ≫ (ρ_ (app F hF η X)).inv := sorry

/-- Composition coherence for the lifted transformation from the identity. -/
theorem naturality_comp :
    ∀ {X Y Z : P.FullSubbicategory} (f : X ⟶ Y) (g : Y ⟶ Z),
      (naturality F hF η (f ≫ g)).hom ≫
          app F hF η X ◁ ((FullSubbicategory.map F hF).mapComp f g).hom =
        ((Pseudofunctor.id P.FullSubbicategory).mapComp f g).hom ▷ app F hF η Z ≫
          (α_ _ _ _).hom ≫
          (Pseudofunctor.id P.FullSubbicategory).map f ◁
            (naturality F hF η g).hom ≫
          (α_ _ _ _).inv ≫
          (naturality F hF η f).hom ▷ (FullSubbicategory.map F hF).map g ≫
          (α_ _ _ _).hom := sorry

end FromId

/-- Lift an ambient strong transformation from the identity to an endopseudofunctor through a
property-selected full subbicategory. -/
def fromId (F : StrictPseudofunctor D D) (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans (Pseudofunctor.id D) F.toPseudofunctor) :
    Pseudofunctor.StrongTrans (Pseudofunctor.id P.FullSubbicategory)
      (FullSubbicategory.map F hF).toPseudofunctor where
  app := FromId.app F hF η
  naturality := FromId.naturality F hF η
  naturality_naturality := FromId.naturality_naturality F hF η
  naturality_id := FromId.naturality_id F hF η
  naturality_comp := FromId.naturality_comp F hF η

/-- The component of `fromId` is the ambient component with the full-subbicategory witness added. -/
@[simp]
theorem fromId.app (F : StrictPseudofunctor D D) (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans (Pseudofunctor.id D) F.toPseudofunctor)
    (X : P.FullSubbicategory) :
    (fromId F hF η).app X = FromId.app F hF η X := sorry

/-- The naturality isomorphism of `fromId` is the ambient naturality isomorphism. -/
@[simp]
theorem fromId.naturality (F : StrictPseudofunctor D D)
    (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans (Pseudofunctor.id D) F.toPseudofunctor)
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (fromId F hF η).naturality f = FromId.naturality F hF η f := sorry

end StrongTrans

end CategoryTheory.ObjectProperty.FullSubbicategory
