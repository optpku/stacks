module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans.LiftTo.Construction
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Computations for source-only full-subbicategory lifts

The component and naturality isomorphism of `StrongTrans.liftTo` forget to the corresponding
data of the ambient transformation.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

universe w v u wA vA uA

namespace ObjectProperty.FullSubbicategory.StrongTrans

variable {D : Type u} [Bicategory.{w, v} D]
variable {P : ObjectProperty D}
variable {A : Type uA} [Bicategory.{wA, vA} A]

/-- A source-only lifted component is the ambient component regarded in the full
subbicategory. -/
@[simp]
theorem liftTo.app
    (G : Pseudofunctor A D) (H : Pseudofunctor A P.FullSubbicategory)
    (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G
      (H.comp (FullSubbicategory.ι P).toPseudofunctor)) (X : A) :
    (liftTo G H hG η).app X =
      Bicategory.InducedBicategory.mkHom (η.app X) := sorry

/-- Forgetting a source-only lifted component recovers the ambient component. -/
@[simp]
theorem liftTo.app.toAmbient
    (G : Pseudofunctor A D) (H : Pseudofunctor A P.FullSubbicategory)
    (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G
      (H.comp (FullSubbicategory.ι P).toPseudofunctor)) (X : A) :
    ((liftTo G H hG η).app X).hom = η.app X := sorry

/-- Source-only lifted naturality is the ambient naturality isomorphism regarded in the full
subbicategory. -/
@[simp]
theorem liftTo.naturality
    (G : Pseudofunctor A D) (H : Pseudofunctor A P.FullSubbicategory)
    (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G
      (H.comp (FullSubbicategory.ι P).toPseudofunctor))
    {X Y : A} (f : X ⟶ Y) :
    (liftTo G H hG η).naturality f =
      Bicategory.InducedBicategory.isoMk (η.naturality f) := sorry

/-- Forgetting the forward naturality cell of `liftTo` recovers the ambient forward cell. -/
@[simp]
theorem liftTo.naturality.hom.toAmbient
    (G : Pseudofunctor A D) (H : Pseudofunctor A P.FullSubbicategory)
    (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G
      (H.comp (FullSubbicategory.ι P).toPseudofunctor))
    {X Y : A} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((liftTo G H hG η).naturality f)).hom =
      (η.naturality f).hom := sorry

/-- Forgetting the inverse naturality cell of `liftTo` recovers the ambient inverse cell. -/
@[simp]
theorem liftTo.naturality.inv.toAmbient
    (G : Pseudofunctor A D) (H : Pseudofunctor A P.FullSubbicategory)
    (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G
      (H.comp (FullSubbicategory.ι P).toPseudofunctor))
    {X Y : A} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((liftTo G H hG η).naturality f)).inv =
      (η.naturality f).inv := sorry

end ObjectProperty.FullSubbicategory.StrongTrans

end CategoryTheory
