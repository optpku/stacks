module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.StrongTrans.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Iso

/-!
# Computations for lifted strong transformations

This leaf exposes the component and naturality data of the generic strong-transformation lift,
both as locally induced data and through the ambient semantic projection.
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

variable (G H : Pseudofunctor A (InducedBicategory D F))
variable (map_mem_G : ∀ {X Y : A} (f : X ⟶ Y),
  Q (G.obj X) (G.obj Y) (G.map f).hom)
variable (map_mem_H : ∀ {X Y : A} (f : X ⟶ Y),
  Q (H.obj X) (H.obj Y) (H.map f).hom)
variable (η : Pseudofunctor.StrongTrans G H)
variable (app_mem : ∀ X : A, Q (G.obj X) (H.obj X) (η.app X).hom)

/-- A lifted component is the original ambient component bundled with its hom-property
witness. -/
@[simp]
theorem lift.app (X : A) :
    (lift G H map_mem_G map_mem_H η app_mem).app X =
      mkHom (η.app X).hom (app_mem X) := sorry

/-- The ambient representative of a lifted component is the original component. -/
@[simp]
theorem lift.app.toAmbient (X : A) :
    ((lift G H map_mem_G map_mem_H η app_mem).app X).obj =
      (η.app X).hom := sorry

/-- Lifted naturality is the original ambient naturality isomorphism bundled by the hom
property. -/
@[simp]
theorem lift.naturality {X Y : A} (f : X ⟶ Y) :
    (lift G H map_mem_G map_mem_H η app_mem).naturality f =
      (Q _ _).isoMk (InducedBicategory.Iso.toAmbient (η.naturality f)) := sorry

/-- The ambient forward cell of lifted naturality is the original forward naturality cell. -/
@[simp]
theorem lift.naturality.hom.toAmbient {X Y : A} (f : X ⟶ Y) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((lift G H map_mem_G map_mem_H η app_mem).naturality f)).hom =
      (InducedBicategory.Iso.toAmbient (η.naturality f)).hom := sorry

/-- The ambient inverse cell of lifted naturality is the original inverse naturality cell. -/
@[simp]
theorem lift.naturality.inv.toAmbient {X Y : A} (f : X ⟶ Y) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((lift G H map_mem_G map_mem_H η app_mem).naturality f)).inv =
      (InducedBicategory.Iso.toAmbient (η.naturality f)).inv := sorry

end StrongTrans

end CategoryTheory.Bicategory.LocallyInducedBicategory
