module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans.LiftFrom.Construction
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Computations for target-only full-subbicategory lifts

The component and naturality isomorphism of `StrongTrans.liftFrom` forget to the corresponding
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

/-- A target-only lifted component is the ambient component regarded in the full
subbicategory. -/
@[simp]
theorem liftFrom.app
    (G : Pseudofunctor A P.FullSubbicategory) (H : Pseudofunctor A D)
    (hH : ∀ X : A, P (H.obj X))
    (η : Pseudofunctor.StrongTrans
      (G.comp (FullSubbicategory.ι P).toPseudofunctor) H) (X : A) :
    (liftFrom G H hH η).app X =
      Bicategory.InducedBicategory.mkHom (η.app X) := sorry

/-- Forgetting a target-only lifted component recovers the ambient component. -/
@[simp]
theorem liftFrom.app.toAmbient
    (G : Pseudofunctor A P.FullSubbicategory) (H : Pseudofunctor A D)
    (hH : ∀ X : A, P (H.obj X))
    (η : Pseudofunctor.StrongTrans
      (G.comp (FullSubbicategory.ι P).toPseudofunctor) H) (X : A) :
    ((liftFrom G H hH η).app X).hom = η.app X := sorry

/-- Target-only lifted naturality is the ambient naturality isomorphism regarded in the full
subbicategory. -/
@[simp]
theorem liftFrom.naturality
    (G : Pseudofunctor A P.FullSubbicategory) (H : Pseudofunctor A D)
    (hH : ∀ X : A, P (H.obj X))
    (η : Pseudofunctor.StrongTrans
      (G.comp (FullSubbicategory.ι P).toPseudofunctor) H)
    {X Y : A} (f : X ⟶ Y) :
    (liftFrom G H hH η).naturality f =
      Bicategory.InducedBicategory.isoMk (η.naturality f) := sorry

/-- Forgetting the forward naturality cell of `liftFrom` recovers the ambient forward cell. -/
@[simp]
theorem liftFrom.naturality.hom.toAmbient
    (G : Pseudofunctor A P.FullSubbicategory) (H : Pseudofunctor A D)
    (hH : ∀ X : A, P (H.obj X))
    (η : Pseudofunctor.StrongTrans
      (G.comp (FullSubbicategory.ι P).toPseudofunctor) H)
    {X Y : A} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((liftFrom G H hH η).naturality f)).hom =
      (η.naturality f).hom := sorry

/-- Forgetting the inverse naturality cell of `liftFrom` recovers the ambient inverse cell. -/
@[simp]
theorem liftFrom.naturality.inv.toAmbient
    (G : Pseudofunctor A P.FullSubbicategory) (H : Pseudofunctor A D)
    (hH : ∀ X : A, P (H.obj X))
    (η : Pseudofunctor.StrongTrans
      (G.comp (FullSubbicategory.ι P).toPseudofunctor) H)
    {X Y : A} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((liftFrom G H hH η).naturality f)).inv =
      (η.naturality f).inv := sorry

end ObjectProperty.FullSubbicategory.StrongTrans

end CategoryTheory
