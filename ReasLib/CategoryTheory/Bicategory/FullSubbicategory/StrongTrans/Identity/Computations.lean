module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrongTrans.Identity
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Computations for identity strong transformations on full subbicategories

This leaf exposes the ambient `2`-cells underlying the naturality isomorphisms of the canonical
`toId` and `fromId` lifts.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty.FullSubbicategory.StrongTrans

variable {D : Type u} [Bicategory.{w, v} D]
variable {P : ObjectProperty D}

/-- The component of `toId` is the ambient component of the transformation. -/
@[simp]
theorem toId.app.toAmbient (F : StrictPseudofunctor D D)
    (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor (Pseudofunctor.id D))
    (X : P.FullSubbicategory) :
    ((toId F hF η).app X).hom = (η.app X.1) := sorry

/-- The forward naturality cell of `toId` is the forward cell of the ambient transformation. -/
@[simp]
theorem toId.naturality.hom.toAmbient (F : StrictPseudofunctor D D)
    (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor (Pseudofunctor.id D))
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((toId F hF η).naturality f)).hom =
      (η.naturality f.hom).hom := sorry

/-- The inverse naturality cell of `toId` is the inverse cell of the ambient transformation. -/
@[simp]
theorem toId.naturality.inv.toAmbient (F : StrictPseudofunctor D D)
    (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor (Pseudofunctor.id D))
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((toId F hF η).naturality f)).inv =
      (η.naturality f.hom).inv := sorry

/-- The component of `fromId` is the ambient component of the transformation. -/
@[simp]
theorem fromId.app.toAmbient (F : StrictPseudofunctor D D)
    (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans (Pseudofunctor.id D) F.toPseudofunctor)
    (X : P.FullSubbicategory) :
    ((fromId F hF η).app X).hom = (η.app X.1) := sorry

/-- The forward naturality cell of `fromId` is the forward cell of the ambient transformation. -/
@[simp]
theorem fromId.naturality.hom.toAmbient (F : StrictPseudofunctor D D)
    (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans (Pseudofunctor.id D) F.toPseudofunctor)
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((fromId F hF η).naturality f)).hom =
      (η.naturality f.hom).hom := sorry

/-- The inverse naturality cell of `fromId` is the inverse cell of the ambient transformation. -/
@[simp]
theorem fromId.naturality.inv.toAmbient (F : StrictPseudofunctor D D)
    (hF : ∀ X : D, P X → P (F.obj X))
    (η : Pseudofunctor.StrongTrans (Pseudofunctor.id D) F.toPseudofunctor)
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((fromId F hF η).naturality f)).inv =
      (η.naturality f.hom).inv := sorry

end CategoryTheory.ObjectProperty.FullSubbicategory.StrongTrans
