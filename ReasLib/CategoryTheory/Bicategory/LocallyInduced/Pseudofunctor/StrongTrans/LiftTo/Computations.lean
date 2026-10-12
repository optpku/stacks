/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor.StrongTrans.LiftTo.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Iso

/-!
# Computations for transformations to locally induced pseudofunctors

These lemmas expose the component and naturality data of `StrongTrans.liftTo` before and after
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

variable (G : Pseudofunctor A (InducedBicategory D F))
variable (H : Pseudofunctor A (LocallyInducedBicategory D F Q))
variable (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
  Q (G.obj X) (G.obj Y) (G.map f).hom)
variable (η : Pseudofunctor.StrongTrans G
  (H.comp (LocallyInducedBicategory.ι D F Q).toPseudofunctor))
variable (app_mem : ∀ X : A, Q (G.obj X) (H.obj X) (η.app X).hom)

/-- A `liftTo` component is the ambient component bundled with its hom-property witness. -/
@[simp]
theorem liftTo.app (X : A) :
    (liftTo G H map_mem η app_mem).app X =
      mkHom (η.app X).hom (app_mem X) := sorry

/-- Forgetting a `liftTo` component recovers the original ambient component. -/
@[simp]
theorem liftTo.app.toAmbient (X : A) :
    ((liftTo G H map_mem η app_mem).app X).obj =
      (η.app X).hom := sorry

/-- Naturality of `liftTo` is the ambient naturality isomorphism bundled by `Q`. -/
@[simp]
theorem liftTo.naturality {X Y : A} (f : X ⟶ Y) :
    (liftTo G H map_mem η app_mem).naturality f =
      (Q _ _).isoMk (InducedBicategory.Iso.toAmbient (η.naturality f)) := sorry

/-- Forgetting the forward `liftTo` naturality cell recovers the ambient forward cell. -/
@[simp]
theorem liftTo.naturality.hom.toAmbient {X Y : A} (f : X ⟶ Y) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((liftTo G H map_mem η app_mem).naturality f)).hom =
      (InducedBicategory.Iso.toAmbient (η.naturality f)).hom := sorry

/-- Forgetting the inverse `liftTo` naturality cell recovers the ambient inverse cell. -/
@[simp]
theorem liftTo.naturality.inv.toAmbient {X Y : A} (f : X ⟶ Y) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((liftTo G H map_mem η app_mem).naturality f)).inv =
      (InducedBicategory.Iso.toAmbient (η.naturality f)).inv := sorry

end StrongTrans

end CategoryTheory.Bicategory.LocallyInducedBicategory
