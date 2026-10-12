/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Indexed open covers and refinements

This module bundles an indexed open cover together with its covering condition.  A morphism
`𝒰 ⟶ 𝒱` records that `𝒱` refines `𝒰`; this orientation is chosen so that refinement maps on
Čech complexes and cohomology are covariant.

The raw refinement category deliberately remembers the selected index map.  Quotienting different
selections belongs in a later coefficient-sensitive layer, after proving that they induce the same
map on cohomology.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u u'

namespace TopologicalSpace

/-- The opposite of the full subcategory of formal coproducts of opens whose indexed family
covers the ambient space. -/
@[stacks 09UZ "indexed open cover"]
abbrev OpenCover.{w, z} (X : Type z) [TopologicalSpace X] :=
  (ObjectProperty.FullSubcategory
    (fun K : FormalCoproduct.{w} (Opens X) ↦ IsOpenCover K.obj))ᵒᵖ

namespace OpenCover

variable {X : Type u} {Y : Type u'} [TopologicalSpace X] [TopologicalSpace Y]

/-- The index type carried by an indexed open cover. -/
abbrev index (𝒰 : OpenCover.{v} X) : Type v := 𝒰.unop.obj.I

/-- The indexed family of opens carried by an indexed open cover. -/
abbrev obj (𝒰 : OpenCover.{v} X) : 𝒰.index → Opens X := 𝒰.unop.obj.obj

/-- The covering condition carried by an indexed open cover. -/
abbrev isCover (𝒰 : OpenCover.{v} X) : IsOpenCover 𝒰.obj := 𝒰.unop.property

/-- The formal coproduct underlying an indexed open cover. -/
abbrev toFormalCoproduct (𝒰 : OpenCover.{v} X) : FormalCoproduct.{v} (Opens X) :=
  𝒰.unop.obj

/-- An indexed open cover coerces to its underlying family of opens. -/
instance instCoeFun : CoeFun (OpenCover.{v} X) fun 𝒰 ↦ 𝒰.index → Opens X where
  coe 𝒰 := 𝒰.obj

/-- Bundle an explicit indexed family satisfying `IsOpenCover`. -/
def ofFamily {I : Type v} (U : I → Opens X) (hU : IsOpenCover U) : OpenCover.{v} X where
  unop := ⟨⟨I, U⟩, hU⟩

/-- The bundled cover constructed from a family has the original index type. -/
@[simp]
theorem ofFamily_index {I : Type v} (U : I → Opens X) (hU : IsOpenCover U) :
    (ofFamily U hU).index = I := sorry

/-- The bundled cover constructed from a family evaluates to the original family. -/
@[simp]
theorem ofFamily_apply {I : Type v} (U : I → Opens X) (hU : IsOpenCover U) (i : I) :
    ofFamily U hU i = U i := sorry

/-- The singleton family consisting of the top open covers the ambient space. -/
theorem top_isCover :
    IsOpenCover (fun _ : PUnit.{v + 1} ↦ (⊤ : Opens X)) := sorry

/-- The canonical one-member open cover by the ambient space. -/
def top : OpenCover.{v} X where
  unop := ⟨⟨PUnit, fun _ ↦ ⊤⟩, top_isCover⟩

/-- The canonical cover by the ambient space evaluates to the top open. -/
@[simp]
theorem top_apply (i : PUnit.{v + 1}) :
    top (X := X) i = ⊤ := sorry

/-- Pull an indexed open cover back along a continuous map. -/
def comap (𝒰 : OpenCover.{v} Y) (f : C(X, Y)) : OpenCover.{v} X where
  unop := ⟨⟨𝒰.index, fun i ↦ (𝒰 i).comap f⟩, 𝒰.isCover.comap f⟩

/-- Pullback preserves the index type of an indexed open cover. -/
@[simp]
theorem comap_index (𝒰 : OpenCover.{v} Y) (f : C(X, Y)) :
    (𝒰.comap f).index = 𝒰.index := sorry

/-- Evaluation of a pulled-back cover is the inverse image of the corresponding open. -/
@[simp]
theorem comap_apply (𝒰 : OpenCover.{v} Y) (f : C(X, Y)) (i : 𝒰.index) :
    𝒰.comap f i = (𝒰 i).comap f := sorry

/-- The formal coproduct underlying an indexed open cover has the same index type. -/
@[simp]
theorem toFormalCoproduct_index (𝒰 : OpenCover.{v} X) :
    𝒰.toFormalCoproduct.index = 𝒰.index := sorry

/-- The formal coproduct underlying an indexed open cover has the same components. -/
@[simp]
theorem toFormalCoproduct_obj (𝒰 : OpenCover.{v} X) (i : 𝒰.index) :
    𝒰.toFormalCoproduct.obj i = 𝒰 i := sorry

/-- Pairwise intersections of two indexed open covers again cover the ambient space. -/
theorem inter_isCover (𝒰 𝒱 : OpenCover.{v} X) :
    IsOpenCover (fun ij : 𝒰.index × 𝒱.index ↦ 𝒰 ij.1 ⊓ 𝒱 ij.2) := sorry

/-- The common refinement of two indexed open covers by all pairwise intersections. -/
@[stacks 09UZ "common intersection refinement of indexed open covers"]
def inter (𝒰 𝒱 : OpenCover.{v} X) : OpenCover.{v} X where
  unop := ⟨⟨𝒰.index × 𝒱.index, fun ij ↦ 𝒰 ij.1 ⊓ 𝒱 ij.2⟩, inter_isCover 𝒰 𝒱⟩

/-- The index type of the common intersection refinement is the product of the two index
types. -/
@[simp]
theorem inter_index (𝒰 𝒱 : OpenCover.{v} X) :
    (inter 𝒰 𝒱).index = (𝒰.index × 𝒱.index) := sorry

/-- A member of the common intersection refinement is the corresponding pairwise
intersection. -/
@[simp]
theorem inter_apply (𝒰 𝒱 : OpenCover.{v} X) (ij : 𝒰.index × 𝒱.index) :
    inter 𝒰 𝒱 ij = 𝒰 ij.1 ⊓ 𝒱 ij.2 := sorry

/-- A morphism from `𝒰` to `𝒱` is the canonical full-subcategory morphism in the opposite
category, and therefore records that `𝒱` refines `𝒰`. -/
@[stacks 09UZ "refinement of indexed open covers"]
abbrev Refinement (𝒰 𝒱 : OpenCover.{v} X) := 𝒰 ⟶ 𝒱

namespace Refinement

variable {𝒰 𝒱 𝒲 𝒵 : OpenCover.{v} X}

/-- The selected index map of a canonical open-cover refinement. -/
abbrev indexMap (r : Refinement 𝒰 𝒱) : 𝒱.index → 𝒰.index := r.unop.hom.f

/-- The componentwise containment carried by a canonical open-cover refinement. -/
abbrev le (r : Refinement 𝒰 𝒱) (j : 𝒱.index) : 𝒱 j ≤ 𝒰 (r.indexMap j) :=
  leOfHom (r.unop.hom.φ j)

/-- Build a canonical open-cover refinement from an index map and componentwise containments. -/
def ofIndexMap (indexMap : 𝒱.index → 𝒰.index)
    (h : ∀ j, 𝒱 j ≤ 𝒰 (indexMap j)) : Refinement 𝒰 𝒱 :=
  Opposite.op (ObjectProperty.homMk
    { f := indexMap, φ := fun j ↦ homOfLE (h j) })

/-- The identity refinement as an explicit operation on canonical open covers. -/
def id (𝒰 : OpenCover.{v} X) : Refinement 𝒰 𝒰 := 𝟙 𝒰

/-- Composition of canonical open-cover refinements as an explicit operation. -/
def comp (r : Refinement 𝒰 𝒱) (s : Refinement 𝒱 𝒲) : Refinement 𝒰 𝒲 := r ≫ s

end Refinement

namespace inter

/-- The common intersection cover refines the left input cover. -/
def fst (𝒰 𝒱 : OpenCover.{v} X) : Refinement 𝒰 (inter 𝒰 𝒱) :=
  Opposite.op (ObjectProperty.homMk
    { f := Prod.fst, φ := fun _ ↦ homOfLE inf_le_left })

/-- The common intersection cover refines the right input cover. -/
def snd (𝒰 𝒱 : OpenCover.{v} X) : Refinement 𝒱 (inter 𝒰 𝒱) :=
  Opposite.op (ObjectProperty.homMk
    { f := Prod.snd, φ := fun _ ↦ homOfLE inf_le_right })

end inter

namespace Refinement

variable {𝒰 𝒱 𝒲 𝒵 : OpenCover.{v} X}

/-- Identity refinement is a left identity for composition. -/
theorem id_comp (r : Refinement 𝒰 𝒱) : comp (id 𝒰) r = r := sorry

/-- Identity refinement is a right identity for composition. -/
theorem comp_id (r : Refinement 𝒰 𝒱) : comp r (id 𝒱) = r := sorry

/-- Composition of selected open-cover refinements is associative. -/
theorem assoc (r : Refinement 𝒰 𝒱) (s : Refinement 𝒱 𝒲) (t : Refinement 𝒲 𝒵) :
    comp (comp r s) t = comp r (comp s t) := sorry

end Refinement

namespace Refinement

variable {𝒰 𝒱 𝒲 : OpenCover.{v} X}

/-- The selected index of an identity refinement is unchanged. -/
@[simp]
theorem id_indexMap (𝒰 : OpenCover.{v} X) (i : 𝒰.index) :
    Refinement.indexMap (Refinement.id 𝒰) i = i := sorry

/-- Selected indices compose in the same order as refinements. -/
@[simp]
theorem comp_indexMap (r : Refinement 𝒰 𝒱) (s : Refinement 𝒱 𝒲) (k : 𝒲.index) :
    Refinement.indexMap (r ≫ s) k = r.indexMap (s.indexMap k) := sorry

/-- A refinement pulls back componentwise along a continuous map. -/
theorem comap_le (r : Refinement 𝒰 𝒱) (f : C(Y, X)) (j : 𝒱.index) :
    (𝒱 j).comap f ≤ (𝒰 (r.indexMap j)).comap f := sorry

/-- Pull back a selected refinement along a continuous map. -/
def comap (r : Refinement 𝒰 𝒱) (f : C(Y, X)) :
    Refinement (𝒰.comap f) (𝒱.comap f) :=
  Refinement.ofIndexMap r.indexMap (r.comap_le f)

/-- Pullback sends the identity refinement to the identity refinement. -/
theorem comap_id (𝒰 : OpenCover.{v} X) (f : C(Y, X)) :
    Refinement.comap (Refinement.id 𝒰) f = Refinement.id (𝒰.comap f) := sorry

/-- Pullback preserves composition of selected refinements. -/
theorem comap_comp (r : Refinement 𝒰 𝒱) (s : Refinement 𝒱 𝒲) (f : C(Y, X)) :
    Refinement.comap (Refinement.comp r s) f =
      Refinement.comp (Refinement.comap r f) (Refinement.comap s f) := sorry

/-- A selected refinement induces the corresponding reverse morphism of formal coproducts of
opens. -/
def toFormalCoproductHom (r : Refinement 𝒰 𝒱) :
    𝒱.toFormalCoproduct ⟶ 𝒰.toFormalCoproduct := r.unop.hom

/-- The formal-coproduct morphism of the identity refinement is the identity. -/
@[simp]
theorem toFormalCoproductHom_id (𝒰 : OpenCover.{v} X) :
    toFormalCoproductHom (Refinement.id 𝒰) = 𝟙 𝒰.toFormalCoproduct := sorry

/-- The formal-coproduct morphism of a composite refinement is the reversed composite of the
corresponding formal-coproduct morphisms. -/
@[simp]
theorem toFormalCoproductHom_comp (r : Refinement 𝒰 𝒱) (s : Refinement 𝒱 𝒲) :
    toFormalCoproductHom (Refinement.comp r s) =
      toFormalCoproductHom s ≫ toFormalCoproductHom r := sorry

end Refinement

/-- Pullback of indexed open covers and their selected refinements along a continuous map. -/
def comapFunctor (f : C(X, Y)) : OpenCover.{v} Y ⥤ OpenCover.{v} X where
  obj 𝒰 := 𝒰.comap f
  map r := Refinement.comap r f
  map_id := Refinement.comap_id (f := f)
  map_comp := fun r s ↦ Refinement.comap_comp r s f

/-- The formal-coproduct bridge sends an identity in the opposite refinement category to an
identity morphism. -/
theorem toFormalCoproductMap_id (𝒰 : (OpenCover.{v} X)ᵒᵖ) :
    Refinement.toFormalCoproductHom (𝟙 𝒰).unop =
      𝟙 𝒰.unop.toFormalCoproduct := sorry

/-- The formal-coproduct bridge preserves composition in the opposite refinement category. -/
theorem toFormalCoproductMap_comp
    {𝒰 𝒱 𝒲 : (OpenCover.{v} X)ᵒᵖ} (r : 𝒰 ⟶ 𝒱) (s : 𝒱 ⟶ 𝒲) :
    Refinement.toFormalCoproductHom (r ≫ s).unop =
      Refinement.toFormalCoproductHom r.unop ≫
        Refinement.toFormalCoproductHom s.unop := sorry

/-- The underlying formal coproduct construction is contravariant in selected refinements. -/
def toFormalCoproductFunctor :
    (OpenCover.{v} X)ᵒᵖ ⥤ FormalCoproduct.{v} (Opens X) where
  obj 𝒰 := 𝒰.unop.toFormalCoproduct
  map r := Refinement.toFormalCoproductHom r.unop
  map_id := toFormalCoproductMap_id
  map_comp := toFormalCoproductMap_comp

end OpenCover

end TopologicalSpace
