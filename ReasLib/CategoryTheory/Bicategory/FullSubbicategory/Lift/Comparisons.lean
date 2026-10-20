module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Comparison cells for full-subbicategory lifts

This leaf records the identity and composition comparison cells of the two
specialized strict lifts.  The statements use the ambient `2`-cells directly,
so downstream code does not need to unfold `map` or `ιOfLE` into `lift`.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u' w' v'

namespace ObjectProperty

variable {D : Type u} [Bicategory.{w, v} D]

namespace FullSubbicategory

variable {P : ObjectProperty D}

section Map

variable {A : Type u'} [Bicategory.{w', v'} A]
variable {Q : ObjectProperty A}

/-- The forward identity comparison of `map` is the forward comparison of the ambient map. -/
@[simp]
theorem map.mapId.hom.toAmbient (F : StrictPseudofunctor A D)
    (hF : ∀ X : A, Q X → P (F.obj X)) (X : Q.FullSubbicategory) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((map F hF).mapId X)).hom =
      (F.mapId X.1).hom := sorry

/-- The inverse identity comparison of `map` is the inverse comparison of the ambient map. -/
@[simp]
theorem map.mapId.inv.toAmbient (F : StrictPseudofunctor A D)
    (hF : ∀ X : A, Q X → P (F.obj X)) (X : Q.FullSubbicategory) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((map F hF).mapId X)).inv =
      (F.mapId X.1).inv := sorry

/-- The forward composition comparison of `map` is the forward ambient comparison. -/
@[simp]
theorem map.mapComp.hom.toAmbient (F : StrictPseudofunctor A D)
    (hF : ∀ X : A, Q X → P (F.obj X))
    {X Y Z : Q.FullSubbicategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((map F hF).mapComp f g)).hom =
      (F.mapComp f.hom g.hom).hom := sorry

/-- The inverse composition comparison of `map` is the inverse ambient comparison. -/
@[simp]
theorem map.mapComp.inv.toAmbient (F : StrictPseudofunctor A D)
    (hF : ∀ X : A, Q X → P (F.obj X))
    {X Y Z : Q.FullSubbicategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((map F hF).mapComp f g)).inv =
      (F.mapComp f.hom g.hom).inv := sorry

end Map

section PropertyInclusion

/-- The forward identity comparison of `ιOfLE` agrees with the ambient inclusion comparison. -/
@[simp]
theorem ιOfLE.mapId.hom.toAmbient {Q : ObjectProperty D} (h : P ≤ Q)
    (X : P.FullSubbicategory) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((ιOfLE h).mapId X)).hom =
      ((ι P).mapId X).hom := sorry

/-- The inverse identity comparison of `ιOfLE` agrees with the ambient inclusion comparison. -/
@[simp]
theorem ιOfLE.mapId.inv.toAmbient {Q : ObjectProperty D} (h : P ≤ Q)
    (X : P.FullSubbicategory) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((ιOfLE h).mapId X)).inv =
      ((ι P).mapId X).inv := sorry

/-- The forward composition comparison of `ιOfLE` agrees with the ambient inclusion comparison. -/
@[simp]
theorem ιOfLE.mapComp.hom.toAmbient {Q : ObjectProperty D} (h : P ≤ Q)
    {X Y Z : P.FullSubbicategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((ιOfLE h).mapComp f g)).hom =
      ((ι P).mapComp f g).hom := sorry

/-- The inverse composition comparison of `ιOfLE` agrees with the ambient inclusion comparison. -/
@[simp]
theorem ιOfLE.mapComp.inv.toAmbient {Q : ObjectProperty D} (h : P ≤ Q)
    {X Y Z : P.FullSubbicategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((ιOfLE h).mapComp f g)).inv =
      ((ι P).mapComp f g).inv := sorry

end PropertyInclusion

end FullSubbicategory

end ObjectProperty

end CategoryTheory
