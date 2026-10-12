/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Lift
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Strong transformations into locally induced bicategories

This file lifts strong transformations whose components satisfy a selected hom
property.  The generic construction works over an arbitrary source bicategory and
arbitrary pseudofunctors.  Specializations at the canonical inclusion provide
transformations to and from the identity pseudofunctor.
-/

@[expose] public section

namespace CategoryTheory.Bicategory.LocallyInducedBicategory

open CategoryTheory ObjectProperty
open scoped CategoryTheory.Bicategory

universe w v u uB wA vA uA

variable {B : Type uB}
variable {D : Type u} [Bicategory.{w, v} D]
variable {F : B → D} {Q : HomProperty F} [Q.IsMultiplicative]

namespace StrongTrans

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {A : Type uA} [Bicategory.{wA, vA} A]

namespace Implementation.Lift
variable (G H : Pseudofunctor A (InducedBicategory D F))
variable (map_mem_G : ∀ {X Y : A} (f : X ⟶ Y),
  Q (G.obj X) (G.obj Y) (G.map f).hom)
variable (map_mem_H : ∀ {X Y : A} (f : X ⟶ Y),
  Q (H.obj X) (H.obj Y) (H.map f).hom)
variable (η : Pseudofunctor.StrongTrans G H)
variable (app_mem : ∀ X : A,
  Q (G.obj X) (H.obj X) (η.app X).hom)

/-- An ambient component satisfying the hom property, bundled as a locally induced
`1`-morphism. -/
private def component (X : A) :
    (liftPseudofunctor G map_mem_G).obj X ⟶
      (liftPseudofunctor H map_mem_H).obj X :=
  mkHom (η.app X).hom (app_mem X)

/-- An ambient naturality isomorphism, bundled in the locally induced hom category. -/
private def naturalityIso {X Y : A} (f : X ⟶ Y) :
    (liftPseudofunctor G map_mem_G).map f ≫
        component G H map_mem_G map_mem_H η app_mem Y ≅
      component G H map_mem_G map_mem_H η app_mem X ≫
        (liftPseudofunctor H map_mem_H).map f :=
  (Q _ _).isoMk (InducedBicategory.Iso.toAmbient (η.naturality f))

/-- Naturality in source `2`-cells for a lifted strong transformation. -/
private theorem naturality₂ {X Y : A} {f g : X ⟶ Y} (τ : f ⟶ g) :
    (liftPseudofunctor G map_mem_G).map₂ τ ▷
        component G H map_mem_G map_mem_H η app_mem Y ≫
        (naturalityIso G H map_mem_G map_mem_H η app_mem g).hom =
      (naturalityIso G H map_mem_G map_mem_H η app_mem f).hom ≫
        component G H map_mem_G map_mem_H η app_mem X ◁
          (liftPseudofunctor H map_mem_H).map₂ τ := sorry

/-- Identity coherence for a lifted strong transformation. -/
private theorem naturalityId (X : A) :
    (naturalityIso G H map_mem_G map_mem_H η app_mem (𝟙 X)).hom ≫
        component G H map_mem_G map_mem_H η app_mem X ◁
          ((liftPseudofunctor H map_mem_H).mapId X).hom =
      ((liftPseudofunctor G map_mem_G).mapId X).hom ▷
          component G H map_mem_G map_mem_H η app_mem X ≫
        (λ_ (component G H map_mem_G map_mem_H η app_mem X)).hom ≫
        (ρ_ (component G H map_mem_G map_mem_H η app_mem X)).inv := sorry

/-- Composition coherence for a lifted strong transformation. -/
private theorem naturalityComp {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (naturalityIso G H map_mem_G map_mem_H η app_mem (f ≫ g)).hom ≫
        component G H map_mem_G map_mem_H η app_mem X ◁
          ((liftPseudofunctor H map_mem_H).mapComp f g).hom =
      ((liftPseudofunctor G map_mem_G).mapComp f g).hom ▷
          component G H map_mem_G map_mem_H η app_mem Z ≫
        (α_ _ _ _).hom ≫
        (liftPseudofunctor G map_mem_G).map f ◁
          (naturalityIso G H map_mem_G map_mem_H η app_mem g).hom ≫
        (α_ _ _ _).inv ≫
        (naturalityIso G H map_mem_G map_mem_H η app_mem f).hom ▷
          (liftPseudofunctor H map_mem_H).map g ≫
        (α_ _ _ _).hom := sorry

end Implementation.Lift

/-- Lift an ambient strong transformation between pseudofunctors into an induced
bicategory when their mapped arrows and the transformation components satisfy the
selected hom property.  The source bicategory is arbitrary. -/
@[stacks 0040 "lift a strong transformation through a hom property"]
def lift
    (G H : Pseudofunctor A (InducedBicategory D F))
    (map_mem_G : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    (map_mem_H : ∀ {X Y : A} (f : X ⟶ Y),
      Q (H.obj X) (H.obj Y) (H.map f).hom)
    (η : Pseudofunctor.StrongTrans G H)
    (app_mem : ∀ X : A,
      Q (G.obj X) (H.obj X) (η.app X).hom) :
    Pseudofunctor.StrongTrans
      (liftPseudofunctor G map_mem_G)
      (liftPseudofunctor H map_mem_H) where
  app := Implementation.Lift.component G H map_mem_G map_mem_H η app_mem
  naturality := Implementation.Lift.naturalityIso G H map_mem_G map_mem_H η app_mem
  naturality_naturality :=
    Implementation.Lift.naturality₂ G H map_mem_G map_mem_H η app_mem
  naturality_id := Implementation.Lift.naturalityId G H map_mem_G map_mem_H η app_mem
  naturality_comp := Implementation.Lift.naturalityComp G H map_mem_G map_mem_H η app_mem
/-- Lift an ambient strong transformation between strict pseudofunctors while retaining the
exact strict-lift pseudofunctors as its source and target.

This is distinct from `StrongTrans.lift`: converting the strict pseudofunctors to arbitrary
pseudofunctors and then lifting them does not definitionally recover
`LocallyInducedBicategory.lift G map_mem_G |>.toPseudofunctor`. -/
@[stacks 0040 "lift a strict strong transformation through a hom property"]
def liftStrict
    (G H : StrictPseudofunctor A (InducedBicategory D F))
    (map_mem_G : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    (map_mem_H : ∀ {X Y : A} (f : X ⟶ Y),
      Q (H.obj X) (H.obj Y) (H.map f).hom)
    (η : Pseudofunctor.StrongTrans G.toPseudofunctor H.toPseudofunctor)
    (app_mem : ∀ X : A, Q (G.obj X) (H.obj X) (η.app X).hom) :
    Pseudofunctor.StrongTrans
      (LocallyInducedBicategory.lift G map_mem_G).toPseudofunctor
      (LocallyInducedBicategory.lift H map_mem_H).toPseudofunctor where
  app := fun X ↦ mkHom (η.app X).hom (app_mem X)
  naturality := fun f ↦
    (Q _ _).isoMk (InducedBicategory.Iso.toAmbient (η.naturality f))
  naturality_naturality := sorry
  naturality_id := sorry
  naturality_comp := sorry

namespace Implementation.ToId

variable (G : StrictPseudofunctor (LocallyInducedBicategory D F Q) (InducedBicategory D F))
variable (map_mem : ∀ {X Y : (LocallyInducedBicategory D F Q)} (f : X ⟶ Y),
  Q (G.obj X) (G.obj Y) (G.map f).hom)
variable (η : Pseudofunctor.StrongTrans G.toPseudofunctor (ι D F Q).toPseudofunctor)
variable (app_mem : ∀ X : (LocallyInducedBicategory D F Q), Q (G.obj X) X (η.app X).hom)

/-- An ambient component satisfying the hom property, bundled as a locally induced
`1`-morphism. -/
private def component (X : LocallyInducedBicategory D F Q) :
    (LocallyInducedBicategory.lift G map_mem).obj X ⟶ X :=
  mkHom (η.app X).hom (app_mem X)

/-- An ambient naturality isomorphism, bundled in the locally induced hom category. -/
private def naturalityIso {X Y : LocallyInducedBicategory D F Q} (f : X ⟶ Y) :
    (LocallyInducedBicategory.lift G map_mem).map f ≫
        component G map_mem η app_mem Y ≅
      component G map_mem η app_mem X ≫ (Pseudofunctor.id (LocallyInducedBicategory D F Q)).map f :=
  (Q _ _).isoMk (InducedBicategory.Iso.toAmbient (η.naturality f))

/-- Naturality in source `2`-cells for a locally induced transformation to the identity. -/
private theorem naturality₂
    {X Y : LocallyInducedBicategory D F Q} {f g : X ⟶ Y} (τ : f ⟶ g) :
    (LocallyInducedBicategory.lift G map_mem).map₂ τ ▷
        component G map_mem η app_mem Y ≫
        (naturalityIso G map_mem η app_mem g).hom =
      (naturalityIso G map_mem η app_mem f).hom ≫
        component G map_mem η app_mem X ◁
          (Pseudofunctor.id (LocallyInducedBicategory D F Q)).map₂ τ := sorry

/-- Identity coherence for a locally induced transformation to the identity. -/
private theorem naturalityId (X : LocallyInducedBicategory D F Q) :
    (naturalityIso G map_mem η app_mem (𝟙 X)).hom ≫
        component G map_mem η app_mem X ◁
          ((Pseudofunctor.id (LocallyInducedBicategory D F Q)).mapId X).hom =
      ((LocallyInducedBicategory.lift G map_mem).mapId X).hom ▷
          component G map_mem η app_mem X ≫
        (λ_ (component G map_mem η app_mem X)).hom ≫
        (ρ_ (component G map_mem η app_mem X)).inv := sorry

/-- Composition coherence for a locally induced transformation to the identity. -/
private theorem naturalityComp
    {X Y Z : LocallyInducedBicategory D F Q} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (naturalityIso G map_mem η app_mem (f ≫ g)).hom ≫
        component G map_mem η app_mem X ◁
          ((Pseudofunctor.id (LocallyInducedBicategory D F Q)).mapComp f g).hom =
      ((LocallyInducedBicategory.lift G map_mem).mapComp f g).hom ▷
          component G map_mem η app_mem Z ≫
        (α_ _ _ _).hom ≫
        (LocallyInducedBicategory.lift G map_mem).map f ◁
          (naturalityIso G map_mem η app_mem g).hom ≫
        (α_ _ _ _).inv ≫
        (naturalityIso G map_mem η app_mem f).hom ▷
          (Pseudofunctor.id (LocallyInducedBicategory D F Q)).map g ≫
        (α_ _ _ _).hom := sorry

end Implementation.ToId
/-- Lift an ambient strong transformation to the canonical inclusion into a locally induced
strong transformation to the identity. -/
@[stacks 0040 "lift a hom-property transformation to the identity"]
def toId (G : StrictPseudofunctor (LocallyInducedBicategory D F Q) (InducedBicategory D F))
    (map_mem : ∀ {X Y : (LocallyInducedBicategory D F Q)} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    (η : Pseudofunctor.StrongTrans G.toPseudofunctor (ι D F Q).toPseudofunctor)
    (app_mem : ∀ X : (LocallyInducedBicategory D F Q), Q (G.obj X) X (η.app X).hom) :
    Pseudofunctor.StrongTrans
      (LocallyInducedBicategory.lift G map_mem).toPseudofunctor
      (Pseudofunctor.id (LocallyInducedBicategory D F Q)) where
  app := Implementation.ToId.component G map_mem η app_mem
  naturality := Implementation.ToId.naturalityIso G map_mem η app_mem
  naturality_naturality := Implementation.ToId.naturality₂ G map_mem η app_mem
  naturality_id := Implementation.ToId.naturalityId G map_mem η app_mem
  naturality_comp := Implementation.ToId.naturalityComp G map_mem η app_mem

namespace Implementation.FromId

variable (G : StrictPseudofunctor (LocallyInducedBicategory D F Q) (InducedBicategory D F))
variable (map_mem : ∀ {X Y : (LocallyInducedBicategory D F Q)} (f : X ⟶ Y),
  Q (G.obj X) (G.obj Y) (G.map f).hom)
variable (η : Pseudofunctor.StrongTrans (ι D F Q).toPseudofunctor G.toPseudofunctor)
variable (app_mem : ∀ X : (LocallyInducedBicategory D F Q), Q X (G.obj X) (η.app X).hom)

/-- An ambient component from the canonical inclusion satisfying the hom property, bundled as
a locally induced `1`-morphism. -/
private def component (X : LocallyInducedBicategory D F Q) :
    X ⟶ (LocallyInducedBicategory.lift G map_mem).obj X :=
  mkHom (η.app X).hom (app_mem X)

/-- An ambient naturality isomorphism from the canonical inclusion, bundled in the locally
induced hom category. -/
private def naturalityIso {X Y : LocallyInducedBicategory D F Q} (f : X ⟶ Y) :
    (Pseudofunctor.id (LocallyInducedBicategory D F Q)).map f ≫ component G map_mem η app_mem Y ≅
      component G map_mem η app_mem X ≫
        (LocallyInducedBicategory.lift G map_mem).map f :=
  (Q _ _).isoMk (InducedBicategory.Iso.toAmbient (η.naturality f))

/-- Naturality in source `2`-cells for a locally induced transformation from the identity. -/
private theorem naturality₂
    {X Y : LocallyInducedBicategory D F Q} {f g : X ⟶ Y} (τ : f ⟶ g) :
    (Pseudofunctor.id (LocallyInducedBicategory D F Q)).map₂ τ ▷
        component G map_mem η app_mem Y ≫
        (naturalityIso G map_mem η app_mem g).hom =
      (naturalityIso G map_mem η app_mem f).hom ≫
        component G map_mem η app_mem X ◁
          (LocallyInducedBicategory.lift G map_mem).map₂ τ := sorry

/-- Identity coherence for a locally induced transformation from the identity. -/
private theorem naturalityId (X : LocallyInducedBicategory D F Q) :
    (naturalityIso G map_mem η app_mem (𝟙 X)).hom ≫
        component G map_mem η app_mem X ◁
          ((LocallyInducedBicategory.lift G map_mem).mapId X).hom =
      ((Pseudofunctor.id (LocallyInducedBicategory D F Q)).mapId X).hom ▷
          component G map_mem η app_mem X ≫
        (λ_ (component G map_mem η app_mem X)).hom ≫
        (ρ_ (component G map_mem η app_mem X)).inv := sorry

/-- Composition coherence for a locally induced transformation from the identity. -/
private theorem naturalityComp
    {X Y Z : LocallyInducedBicategory D F Q} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (naturalityIso G map_mem η app_mem (f ≫ g)).hom ≫
        component G map_mem η app_mem X ◁
          ((LocallyInducedBicategory.lift G map_mem).mapComp f g).hom =
      ((Pseudofunctor.id (LocallyInducedBicategory D F Q)).mapComp f g).hom ▷
          component G map_mem η app_mem Z ≫
        (α_ _ _ _).hom ≫
        (Pseudofunctor.id (LocallyInducedBicategory D F Q)).map f ◁
          (naturalityIso G map_mem η app_mem g).hom ≫
        (α_ _ _ _).inv ≫
        (naturalityIso G map_mem η app_mem f).hom ▷
          (LocallyInducedBicategory.lift G map_mem).map g ≫
        (α_ _ _ _).hom := sorry

end Implementation.FromId
/-- Lift an ambient strong transformation from the canonical inclusion into a locally induced
strong transformation from the identity. -/
@[stacks 0040 "lift a hom-property transformation from the identity"]
def fromId (G : StrictPseudofunctor (LocallyInducedBicategory D F Q) (InducedBicategory D F))
    (map_mem : ∀ {X Y : (LocallyInducedBicategory D F Q)} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    (η : Pseudofunctor.StrongTrans (ι D F Q).toPseudofunctor G.toPseudofunctor)
    (app_mem : ∀ X : (LocallyInducedBicategory D F Q), Q X (G.obj X) (η.app X).hom) :
    Pseudofunctor.StrongTrans (Pseudofunctor.id (LocallyInducedBicategory D F Q))
      (LocallyInducedBicategory.lift G map_mem).toPseudofunctor where
  app := Implementation.FromId.component G map_mem η app_mem
  naturality := Implementation.FromId.naturalityIso G map_mem η app_mem
  naturality_naturality := Implementation.FromId.naturality₂ G map_mem η app_mem
  naturality_id := Implementation.FromId.naturalityId G map_mem η app_mem
  naturality_comp := Implementation.FromId.naturalityComp G map_mem η app_mem

end StrongTrans

end CategoryTheory.Bicategory.LocallyInducedBicategory
