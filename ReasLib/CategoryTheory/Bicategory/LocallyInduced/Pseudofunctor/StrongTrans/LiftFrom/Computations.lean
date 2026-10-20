/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor.StrongTrans.LiftFrom.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Iso

/-!
# Computations for transformations from locally induced pseudofunctors

These lemmas expose the component and naturality data of `StrongTrans.liftFrom` before and after
forgetting the locally induced hom-property witnesses.
-/

@[expose] public section

universe w v u uB wA vA uA

namespace CategoryTheory.Bicategory.LocallyInducedBicategory

open CategoryTheory ObjectProperty
open scoped CategoryTheory.Bicategory

variable {B : Type uB}
variable {D : Type u} [Bicategory.{w, v} D]
variable {F : B → D} {Q : HomProperty F} [Q.IsMultiplicative]
variable {A : Type uA} [Bicategory.{wA, vA} A]

namespace StrongTrans

variable (G : Pseudofunctor A (LocallyInducedBicategory D F Q))
variable (H : Pseudofunctor A (InducedBicategory D F))
variable (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
  Q (H.obj X) (H.obj Y) (H.map f).hom)
variable (η : Pseudofunctor.StrongTrans
  (G.comp (LocallyInducedBicategory.ι D F Q).toPseudofunctor) H)
variable (app_mem : ∀ X : A, Q (G.obj X) (H.obj X) (η.app X).hom)

/-- A `liftFrom` component is the ambient component bundled with its hom-property witness. -/
@[simp]
theorem liftFrom.app (X : A) :
    (liftFrom G H map_mem η app_mem).app X =
      mkHom (η.app X).hom (app_mem X) := sorry

/-- Forgetting a `liftFrom` component recovers the original ambient component. -/
@[simp]
theorem liftFrom.app.toAmbient (X : A) :
    ((liftFrom G H map_mem η app_mem).app X).obj =
      (η.app X).hom := sorry

/-- Naturality of `liftFrom` is the ambient naturality isomorphism bundled by `Q`. -/
@[simp]
theorem liftFrom.naturality {X Y : A} (f : X ⟶ Y) :
    (liftFrom G H map_mem η app_mem).naturality f =
      (Q _ _).isoMk (InducedBicategory.Iso.toAmbient (η.naturality f)) := sorry

/-- Forgetting the forward `liftFrom` naturality cell recovers the ambient forward cell through
the canonical induced-bicategory projection. -/
@[simp]
theorem liftFrom.naturality.hom.toAmbient {X Y : A} (f : X ⟶ Y) :
    (Bicategory.LocallyInducedBicategory.Iso.toAmbient
      ((liftFrom G H map_mem η app_mem).naturality f)).hom =
      (Bicategory.InducedBicategory.Iso.toAmbient (η.naturality f)).hom := sorry

/-- Forgetting the inverse `liftFrom` naturality cell recovers the ambient inverse cell through
the canonical induced-bicategory projection. -/
@[simp]
theorem liftFrom.naturality.inv.toAmbient {X Y : A} (f : X ⟶ Y) :
    (Bicategory.LocallyInducedBicategory.Iso.toAmbient
      ((liftFrom G H map_mem η app_mem).naturality f)).inv =
      (Bicategory.InducedBicategory.Iso.toAmbient (η.naturality f)).inv := sorry

end StrongTrans

end CategoryTheory.Bicategory.LocallyInducedBicategory
