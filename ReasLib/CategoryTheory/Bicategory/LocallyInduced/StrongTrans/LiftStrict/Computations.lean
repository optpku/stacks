module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.StrongTrans.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Iso

/-!
# Computations for strictly lifted strong transformations

This leaf exposes the component and naturality data of liftStrict while preserving the exact
strict-lift source and target pseudofunctors.
-/

@[expose] public section

namespace CategoryTheory.Bicategory.LocallyInducedBicategory

open CategoryTheory ObjectProperty
open scoped CategoryTheory.Bicategory

universe w v u uB wA vA uA

variable {B : Type uB}
variable {D : Type u} [Bicategory.{w, v} D]
variable {F : B → D} {Q : HomProperty F} [Q.IsMultiplicative]
variable {A : Type uA} [Bicategory.{wA, vA} A]

namespace StrongTrans

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable (G H : StrictPseudofunctor A (InducedBicategory D F))
variable (map_mem_G : ∀ {X Y : A} (f : X ⟶ Y),
  Q (G.obj X) (G.obj Y) (G.map f).hom)
variable (map_mem_H : ∀ {X Y : A} (f : X ⟶ Y),
  Q (H.obj X) (H.obj Y) (H.map f).hom)
variable (η : Pseudofunctor.StrongTrans G.toPseudofunctor H.toPseudofunctor)
variable (app_mem : ∀ X : A, Q (G.obj X) (H.obj X) (η.app X).hom)

/-- A strict-lifted component is the original ambient component bundled with its hom-property
witness. -/
@[simp]
theorem liftStrict.app (X : A) :
    (liftStrict G H map_mem_G map_mem_H η app_mem).app X =
      mkHom (η.app X).hom (app_mem X) := sorry

/-- The ambient representative of a strict-lifted component is the original component. -/
@[simp]
theorem liftStrict.app.toAmbient (X : A) :
    ((liftStrict G H map_mem_G map_mem_H η app_mem).app X).obj =
      (η.app X).hom := sorry

/-- Strict-lifted naturality is the original ambient naturality isomorphism bundled by the
hom-property. -/
@[simp]
theorem liftStrict.naturality {X Y : A} (f : X ⟶ Y) :
    (liftStrict G H map_mem_G map_mem_H η app_mem).naturality f =
      (Q _ _).isoMk (InducedBicategory.Iso.toAmbient (η.naturality f)) := sorry

/-- The ambient forward naturality cell of a strict lift is the original forward cell. -/
@[simp]
theorem liftStrict.naturality.hom.toAmbient {X Y : A} (f : X ⟶ Y) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((liftStrict G H map_mem_G map_mem_H η app_mem).naturality f)).hom =
      (InducedBicategory.Iso.toAmbient (η.naturality f)).hom := sorry

/-- The ambient inverse naturality cell of a strict lift is the original inverse cell. -/
@[simp]
theorem liftStrict.naturality.inv.toAmbient {X Y : A} (f : X ⟶ Y) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((liftStrict G H map_mem_G map_mem_H η app_mem).naturality f)).inv =
      (InducedBicategory.Iso.toAmbient (η.naturality f)).inv := sorry

end StrongTrans

end CategoryTheory.Bicategory.LocallyInducedBicategory
