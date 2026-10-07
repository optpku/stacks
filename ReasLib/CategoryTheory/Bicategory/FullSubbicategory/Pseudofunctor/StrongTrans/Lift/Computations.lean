module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans.Lift.Construction
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Computations for strong transformations between lifted pseudofunctors

These lemmas expose the component and both naturality cells before and after forgetting the
full-subbicategory wrapper.
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

/-- A lifted component is the ambient component with the full-subbicategory wrapper added. -/
@[simp]
theorem liftPseudofunctor.app
    (F G : Pseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F G) (X : A) :
    (liftPseudofunctor F G hF hG η).app X =
      Bicategory.InducedBicategory.mkHom (η.app X) := sorry

/-- Forgetting a lifted component recovers the original ambient component. -/
@[simp]
theorem liftPseudofunctor.app.toAmbient
    (F G : Pseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F G) (X : A) :
    ((liftPseudofunctor F G hF hG η).app X).hom = η.app X := sorry

/-- Lifted naturality is the ambient naturality isomorphism with the wrapper added. -/
@[simp]
theorem liftPseudofunctor.naturality
    (F G : Pseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F G) {X Y : A} (f : X ⟶ Y) :
    (liftPseudofunctor F G hF hG η).naturality f =
      Bicategory.InducedBicategory.isoMk (η.naturality f) := sorry

/-- Forgetting the forward lifted naturality cell recovers the ambient forward cell. -/
@[simp]
theorem liftPseudofunctor.naturality.hom.toAmbient
    (F G : Pseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F G) {X Y : A} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((liftPseudofunctor F G hF hG η).naturality f)).hom =
      (η.naturality f).hom := sorry

/-- Forgetting the inverse lifted naturality cell recovers the ambient inverse cell. -/
@[simp]
theorem liftPseudofunctor.naturality.inv.toAmbient
    (F G : Pseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F G) {X Y : A} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient
      ((liftPseudofunctor F G hF hG η).naturality f)).inv =
      (η.naturality f).inv := sorry

end ObjectProperty.FullSubbicategory.StrongTrans

end CategoryTheory
