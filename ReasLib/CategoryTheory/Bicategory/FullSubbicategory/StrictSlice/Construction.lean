/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Bicategory.StrictSlice.Map
public import ReasLib.CategoryTheory.Bicategory.StrictSlice.ObjectProperty
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict slices of full subbicategories

For an object property `P` and `X : P.FullSubbicategory`, the strict slice of `X`
inside the full subbicategory has the same data as the full subbicategory of the ambient
strict slice selected by `P.strictSlice X.1`.

The forward strict pseudofunctor reuses `Bicategory.StrictSlice.map` and
`FullSubbicategory.lift`. The reverse direction only repackages the ambient slice data;
it does not choose objects, morphisms, or cells.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe w v u

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

namespace ObjectProperty.FullSubbicategory.StrictSlice

variable {D : Type u} [Bicategory.{w, v} D] [Bicategory.Strict D]
variable (P : ObjectProperty D) (X : P.FullSubbicategory)

/-- Forget the object-property witnesses in a strict slice and retain the property of each
domain as a target full-subbicategory witness. -/
def toAmbient :
    StrictPseudofunctor (Bicategory.StrictSlice X)
      (P.strictSlice X.1).FullSubbicategory :=
  FullSubbicategory.lift
    (Bicategory.StrictSlice.map (FullSubbicategory.ι P) X)
    (fun S => S.obj.property)

namespace toAmbient

/-- The ambient strict-slice object underlying the forward image is the canonical mapped
strict-slice object. -/
@[simp]
theorem obj_val (S : Bicategory.StrictSlice X) :
    ((toAmbient P X).obj S).1 =
      Bicategory.StrictSlice.Map.obj (FullSubbicategory.ι P) S := sorry

/-- The domain of a forward image is the ambient domain of the original slice object. -/
@[simp]
theorem obj_obj (S : Bicategory.StrictSlice X) :
    ((toAmbient P X).obj S).1.obj = S.obj.1 := sorry

/-- The structural arrow of a forward image is the ambient structural arrow of the original
slice object. -/
@[simp]
theorem obj_hom (S : Bicategory.StrictSlice X) :
    ((toAmbient P X).obj S).1.hom = (FullSubbicategory.ι P).map S.hom := sorry

/-- The ambient map of a forward image is the ambient map of the original slice morphism. -/
@[simp]
theorem map_hom {S T : Bicategory.StrictSlice X} (f : S ⟶ T) :
    Bicategory.StrictSlice.Hom.hom ((toAmbient P X).map f).hom =
      (Bicategory.StrictSlice.Hom.hom f).hom := sorry

/-- The ambient cell of a forward image is the ambient cell of the original slice
`2`-morphism. -/
@[simp]
theorem map₂_hom
    {S T : Bicategory.StrictSlice X} {f g : S ⟶ T} (eta : f ⟶ g) :
    Bicategory.StrictSlice.Hom₂.hom ((toAmbient P X).map₂ eta).hom =
      (Bicategory.StrictSlice.Hom₂.hom eta).hom := sorry

end toAmbient

namespace OfAmbient

variable {P X}

/-- Repackage an ambient strict-slice object whose domain satisfies `P` as a strict-slice
object internal to `P.FullSubbicategory`. -/
def obj (S : (P.strictSlice X.1).FullSubbicategory) :
    Bicategory.StrictSlice X :=
  Bicategory.StrictSlice.mk
    (FullSubbicategory.mk P S.1.obj S.property)
    (Bicategory.InducedBicategory.mkHom S.1.hom)

/-- Repackage the ambient map of an ambient strict-slice morphism as a morphism between the
repackaged domains. -/
def map {S T : (P.strictSlice X.1).FullSubbicategory} (f : S ⟶ T) :
    (obj S).obj ⟶ (obj T).obj :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.StrictSlice.Hom.hom f.hom)

/-- The repackaged ambient map commutes with the repackaged structural arrows. -/
private theorem homComm
    {S T : (P.strictSlice X.1).FullSubbicategory} (f : S ⟶ T) :
    map f ≫ (obj T).hom =
      (obj S).hom := sorry

/-- Repackage an ambient strict-slice morphism as a strict-slice morphism internal to the full
subbicategory. -/
def hom {S T : (P.strictSlice X.1).FullSubbicategory} (f : S ⟶ T) :
    obj S ⟶ obj T :=
  Bicategory.StrictSlice.Hom.mk (map f) (homComm f)

/-- Repackage the ambient cell of an ambient strict-slice `2`-morphism as a cell between the
repackaged domain maps. -/
def map₂
    {S T : (P.strictSlice X.1).FullSubbicategory}
    {f g : S ⟶ T} (eta : f ⟶ g) :
    map f ⟶ map g :=
  Bicategory.InducedBicategory.mkHom₂
    (Bicategory.StrictSlice.Hom₂.hom eta.hom)

/-- The repackaged ambient cell is compatible with the repackaged commuting triangles. -/
private theorem hom₂Comm
    {S T : (P.strictSlice X.1).FullSubbicategory}
    {f g : S ⟶ T} (eta : f ⟶ g) :
    map₂ eta ▷ (obj T).hom ≫
        eqToHom (Bicategory.StrictSlice.Hom.comm (hom g)) =
      eqToHom (Bicategory.StrictSlice.Hom.comm (hom f)) := sorry

/-- Repackage an ambient strict-slice `2`-morphism as a `2`-morphism internal to the full
subbicategory. -/
def hom₂
    {S T : (P.strictSlice X.1).FullSubbicategory}
    {f g : S ⟶ T} (eta : f ⟶ g) :
    hom f ⟶ hom g :=
  Bicategory.StrictSlice.Hom₂.mk (map₂ eta) (hom₂Comm eta)

/-- Forgetting the property witness from a repackaged domain recovers the original ambient
domain. -/
@[simp]
theorem obj_obj (S : (P.strictSlice X.1).FullSubbicategory) :
    (obj S).obj.1 = S.1.obj := sorry

/-- The ambient structural arrow of a repackaged object is the original structural arrow. -/
@[simp]
theorem obj_hom (S : (P.strictSlice X.1).FullSubbicategory) :
    (FullSubbicategory.ι P).map (obj S).hom = S.1.hom := sorry

/-- The ambient map of a repackaged morphism is the original ambient map. -/
@[simp]
theorem map_hom
    {S T : (P.strictSlice X.1).FullSubbicategory} (f : S ⟶ T) :
    (map f).hom = Bicategory.StrictSlice.Hom.hom f.hom := sorry

/-- The ambient cell of a repackaged domain cell is the original ambient cell. -/
@[simp]
theorem map₂_hom
    {S T : (P.strictSlice X.1).FullSubbicategory}
    {f g : S ⟶ T} (eta : f ⟶ g) :
    (map₂ eta).hom = Bicategory.StrictSlice.Hom₂.hom eta.hom := sorry

/-- The ambient map of a repackaged strict-slice morphism is the original ambient map. -/
@[simp]
theorem hom_hom
    {S T : (P.strictSlice X.1).FullSubbicategory} (f : S ⟶ T) :
    (Bicategory.StrictSlice.Hom.hom (hom f)).hom =
      Bicategory.StrictSlice.Hom.hom f.hom := sorry

/-- The ambient cell of a repackaged `2`-morphism is the original ambient cell. -/
@[simp]
theorem hom₂_hom
    {S T : (P.strictSlice X.1).FullSubbicategory}
    {f g : S ⟶ T} (eta : f ⟶ g) :
    (Bicategory.StrictSlice.Hom₂.hom (hom₂ eta)).hom =
      Bicategory.StrictSlice.Hom₂.hom eta.hom := sorry

/-- Repackaging preserves identity morphisms strictly. -/
private theorem homId (S : (P.strictSlice X.1).FullSubbicategory) :
    hom (𝟙 S) = 𝟙 (obj S) := sorry

/-- Repackaging preserves composition of morphisms strictly. -/
private theorem homComp
    {R S T : (P.strictSlice X.1).FullSubbicategory}
    (f : R ⟶ S) (g : S ⟶ T) :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- Repackaging preserves identity `2`-morphisms. -/
private theorem hom₂Id
    {S T : (P.strictSlice X.1).FullSubbicategory} (f : S ⟶ T) :
    hom₂ (𝟙 f) = 𝟙 (hom f) := sorry

/-- Repackaging preserves vertical composition of `2`-morphisms. -/
private theorem hom₂Comp
    {S T : (P.strictSlice X.1).FullSubbicategory}
    {f g h : S ⟶ T} (eta : f ⟶ g) (theta : g ⟶ h) :
    hom₂ (eta ≫ theta) = hom₂ eta ≫ hom₂ theta := sorry

/-- Repackaging is compatible with left whiskering. -/
private theorem hom₂WhiskerLeft
    {R S T : (P.strictSlice X.1).FullSubbicategory}
    (f : R ⟶ S) {g h : S ⟶ T} (eta : g ⟶ h) :
    hom₂ (f ◁ eta) =
      eqToHom (homComp f g) ≫ hom f ◁ hom₂ eta ≫
        eqToHom (homComp f h).symm := sorry

/-- Repackaging is compatible with right whiskering. -/
private theorem hom₂WhiskerRight
    {R S T : (P.strictSlice X.1).FullSubbicategory}
    {f g : R ⟶ S} (eta : f ⟶ g) (h : S ⟶ T) :
    hom₂ (eta ▷ h) =
      eqToHom (homComp f h) ≫ hom₂ eta ▷ hom h ≫
        eqToHom (homComp g h).symm := sorry

/-- The strict-pseudofunctor data for ambient-to-internal slice repackaging. -/
private def preCore (P : ObjectProperty D) (X : P.FullSubbicategory) :
    StrictPseudofunctorPreCore
      (P.strictSlice X.1).FullSubbicategory (Bicategory.StrictSlice X) where
  obj := obj
  map := hom
  map₂ := hom₂
  map_id := homId
  map_comp := homComp
  map₂_id := hom₂Id
  map₂_comp := hom₂Comp
  map₂_whisker_left := hom₂WhiskerLeft
  map₂_whisker_right := hom₂WhiskerRight

end OfAmbient

/-- Repackage the full subbicategory of the ambient strict slice as the strict slice internal
to the full subbicategory. -/
def ofAmbient :
    StrictPseudofunctor (P.strictSlice X.1).FullSubbicategory
      (Bicategory.StrictSlice X) :=
  StrictPseudofunctor.mk'' (OfAmbient.preCore P X)

namespace ofAmbient

/-- The object action of `ofAmbient` is the explicit repackaging owner. -/
@[simp]
theorem obj (S : (P.strictSlice X.1).FullSubbicategory) :
    (ofAmbient P X).obj S = OfAmbient.obj S := sorry

/-- The morphism action of `ofAmbient` is the explicit repackaging owner. -/
@[simp]
theorem map {S T : (P.strictSlice X.1).FullSubbicategory} (f : S ⟶ T) :
    (ofAmbient P X).map f = OfAmbient.hom f := sorry

/-- The `2`-morphism action of `ofAmbient` is the explicit repackaging owner. -/
@[simp]
theorem map₂
    {S T : (P.strictSlice X.1).FullSubbicategory}
    {f g : S ⟶ T} (eta : f ⟶ g) :
    (ofAmbient P X).map₂ eta = OfAmbient.hom₂ eta := sorry

end ofAmbient

/- Data audit: `toAmbient` reuses strict-slice mapping and the generic full-subbicategory lift.
`OfAmbient.obj`, `OfAmbient.map`, and `OfAmbient.map₂` explicitly repackage the supplied
ambient object, morphism, and cell data; `OfAmbient.hom` and `OfAmbient.hom₂` only attach the
required commuting proof fields. Any `sorryAx` is confined to equality and coherence fields. -/

end ObjectProperty.FullSubbicategory.StrictSlice

end CategoryTheory
