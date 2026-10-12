/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Construction
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Computations for full-subbicategory lifts

This module exposes the object, `1`-cell, `2`-cell, and strict-comparison
actions of the canonical lifts and property-implication inclusions. It also
records their strict factorization laws so downstream constructions need not
unfold coherence-bearing pseudofunctor structures.
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

section Lift

variable {A : Type u'} [Bicategory.{w', v'} A]

/-- The object action of `lift` is the explicitly packaged ambient object and its membership
witness. -/
@[simp]
theorem lift.obj (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X)) (X : A) :
    (lift G obj_mem).obj X = mk P (G.obj X) (obj_mem X) := sorry

/-- The ambient representative of a `1`-morphism mapped by `lift` is the ambient image under
the original strict pseudofunctor. -/
@[simp]
theorem lift.map.toAmbient (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} (f : X ⟶ Y) :
    ((lift G obj_mem).map f).hom = G.map f := sorry

/-- The ambient representative of a `2`-morphism mapped by `lift` is its original image. -/
@[simp]
theorem lift.map₂.toAmbient (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} {f g : X ⟶ Y} (η : f ⟶ g) :
    ((lift G obj_mem).map₂ η).hom = G.map₂ η := sorry

/-- The ambient forward identity comparison of `lift` is the identity comparison of the
original strict pseudofunctor. -/
@[simp]
theorem lift.mapId.hom.toAmbient (G : StrictPseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    (X : A) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((lift G obj_mem).mapId X)).hom =
      (G.mapId X).hom := sorry

/-- The ambient inverse identity comparison of `lift` is the identity comparison of the
original strict pseudofunctor. -/
@[simp]
theorem lift.mapId.inv.toAmbient (G : StrictPseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    (X : A) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((lift G obj_mem).mapId X)).inv =
      (G.mapId X).inv := sorry

/-- The ambient forward composition comparison of `lift` is the composition comparison of the
original strict pseudofunctor. -/
@[simp]
theorem lift.mapComp.hom.toAmbient (G : StrictPseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((lift G obj_mem).mapComp f g)).hom =
      (G.mapComp f g).hom := sorry

/-- The ambient inverse composition comparison of `lift` is the composition comparison of the
original strict pseudofunctor. -/
@[simp]
theorem lift.mapComp.inv.toAmbient (G : StrictPseudofunctor A D)
    (obj_mem : ∀ X : A, P (G.obj X))
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Bicategory.InducedBicategory.Iso.toAmbient ((lift G obj_mem).mapComp f g)).inv =
      (G.mapComp f g).inv := sorry

/-- Forgetting the membership witnesses after `lift` recovers the original strict
pseudofunctor. -/
theorem lift.comp_ι (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X)) :
    (lift G obj_mem).comp (ι P) = G := sorry

end Lift

section Map

variable {A : Type u'} [Bicategory.{w', v'} A]
variable {Q : ObjectProperty A}

/-- The object action of `map` applies the ambient strict pseudofunctor and equips its image with
the supplied target-property witness. -/
@[simp]
theorem map.obj (F : StrictPseudofunctor A D) (hF : ∀ X : A, Q X → P (F.obj X))
    (X : Q.FullSubbicategory) :
    (map F hF).obj X = mk P (F.obj X.1) (hF X.1 X.property) := sorry

/-- Forgetting the target-property witness from the image of a `1`-morphism under `map`
recovers the ambient image of its source representative. -/
@[simp]
theorem map.toAmbient (F : StrictPseudofunctor A D)
    (hF : ∀ X : A, Q X → P (F.obj X))
    {X Y : Q.FullSubbicategory} (f : X ⟶ Y) :
    ((map F hF).map f).hom = F.map f.hom := sorry

/-- Forgetting the target-property witness from the image of a `2`-morphism under `map`
recovers the ambient image of its source representative. -/
@[simp]
theorem map.map₂.toAmbient (F : StrictPseudofunctor A D)
    (hF : ∀ X : A, Q X → P (F.obj X))
    {X Y : Q.FullSubbicategory} {f g : X ⟶ Y} (eta : f ⟶ g) :
    ((map F hF).map₂ eta).hom = F.map₂ eta.hom := sorry

/-- Forgetting the target property after applying `map` recovers the ambient strict
pseudofunctor after forgetting the source property. -/
theorem map.comp_ι (F : StrictPseudofunctor A D) (hF : ∀ X : A, Q X → P (F.obj X)) :
    (map F hF).comp (ι P) = (ι Q).comp F := sorry

end Map

section PropertyInclusion

/-- The property-implication inclusion packages an object with the target property supplied by
the implication. -/
@[simp]
theorem ιOfLE.obj {Q : ObjectProperty D} (h : P ≤ Q) (X : P.FullSubbicategory) :
    (ιOfLE h).obj X = mk Q X.1 (h X.1 X.property) := sorry

/-- The ambient representative of a `1`-morphism is unchanged by a property-implication
inclusion. -/
@[simp]
theorem ιOfLE.map.toAmbient {Q : ObjectProperty D} (h : P ≤ Q)
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    ((ιOfLE h).map f).hom = f.hom := sorry

/-- The ambient representative of a `2`-morphism is unchanged by a property-implication
inclusion. -/
@[simp]
theorem ιOfLE.map₂.toAmbient {Q : ObjectProperty D} (h : P ≤ Q)
    {X Y : P.FullSubbicategory} {f g : X ⟶ Y} (η : f ⟶ g) :
    ((ιOfLE h).map₂ η).hom = η.hom := sorry

/-- Composing a property-implication inclusion with the ambient inclusion gives the original
ambient inclusion. -/
theorem ιOfLE.comp_ι {Q : ObjectProperty D} (h : P ≤ Q) :
    (ιOfLE h).comp (ι Q) = ι P := sorry

/-- An inclusion induced by an implication from an object property to itself is the identity at
the pseudofunctor layer. -/
theorem ιOfLE.eq_id (h : P ≤ P) :
    (ιOfLE h).toPseudofunctor =
      (StrictPseudofunctor.id P.FullSubbicategory).toPseudofunctor := sorry

/-- Successive property-implication inclusions agree with the inclusion induced by their
composite implication. -/
theorem ιOfLE.comp {Q R : ObjectProperty D} (hPQ : P ≤ Q) (hQR : Q ≤ R) :
    (ιOfLE hPQ).toPseudofunctor.comp (ιOfLE hQR).toPseudofunctor =
      (ιOfLE (hPQ.trans hQR)).toPseudofunctor := sorry

end PropertyInclusion

end FullSubbicategory

end ObjectProperty

end CategoryTheory
