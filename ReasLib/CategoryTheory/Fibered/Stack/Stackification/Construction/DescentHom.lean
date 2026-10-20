/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.DescentObjects
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Gluing morphisms between cover descent objects

Representatives of the supplied local morphisms determine an actual bound
cover and component arrows. The original prestack condition makes these
components commute globally with the original descent data. It is an explicit
input to that law; no fullness or Hom-gluing witness is assumed for the new
category.
-/

@[expose] public section

open CategoryTheory Opposite GrothendieckTopology

noncomputable section

universe u v uF vF

namespace CategoryTheory.Functor.StackificationConstruction.DescentCompletion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF})

/-- A supplied native descent morphism has actual raw representatives on each
outer covering arrow. -/
def homRepresentative {U : C} (R : J.Cover U) {a b : Object J F U}
    (φ : ((presheaf J F).toPseudofunctor'.toDescentData
      (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj a ⟶
      ((presheaf J F).toPseudofunctor'.toDescentData
        (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj b)
    (I : R.Arrow) : RawHom J F (pullbackObject J F I.f a) (pullbackObject J F I.f b) :=
  _root_.Quotient.out (φ.hom (Presieve.categoryMk (R : Sieve U).arrows I.f I.hf))

def homFlattenCover {U : C} (R : J.Cover U) {a b : Object J F U}
    (φ : ((presheaf J F).toPseudofunctor'.toDescentData
      (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj a ⟶
      ((presheaf J F).toPseudofunctor'.toDescentData
        (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj b) : J.Cover U :=
  R.bind fun I ↦ (homRepresentative J F R φ I).cover

/-- Membership in each original cover follows from the supplied raw maps. -/
theorem homFlattenCover_left {U : C} (R : J.Cover U) {a b : Object J F U}
    (φ : ((presheaf J F).toPseudofunctor'.toDescentData
      (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj a ⟶
      ((presheaf J F).toPseudofunctor'.toDescentData
        (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj b) :
    homFlattenCover J F R φ ≤ a.cover := sorry

theorem homFlattenCover_right {U : C} (R : J.Cover U) {a b : Object J F U}
    (φ : ((presheaf J F).toPseudofunctor'.toDescentData
      (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj a ⟶
      ((presheaf J F).toPseudofunctor'.toDescentData
        (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj b) :
    homFlattenCover J F R φ ≤ b.cover := sorry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The component of the flattened arrow is the actual local component after
transport along the native bind factorization equation. -/
def homFlattenComponent {U : C} (R : J.Cover U) {a b : Object J F U}
    (φ : ((presheaf J F).toPseudofunctor'.toDescentData
      (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj a ⟶
      ((presheaf J F).toPseudofunctor'.toDescentData
        (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj b)
    (K : (homFlattenCover J F R φ).Arrow) :
    (restrictDatum J F a.datum (homFlattenCover_left J F R φ)).obj K ⟶
      (restrictDatum J F b.datum (homFlattenCover_right J F R φ)).obj K := by
  let I := K.fromMiddle
  let L := K.toMiddle
  let raw := homRepresentative J F R φ I
  let ia : {f : K.Y ⟶ U // a.cover f} := ⟨L.f ≫ I.f, raw.left _ L.hf⟩
  let ib : {f : K.Y ⟶ U // b.cover f} := ⟨L.f ≫ I.f, raw.right _ L.hf⟩
  let sourceEq : (⟨K.f, homFlattenCover_left J F R φ K.f K.hf⟩ : {f : K.Y ⟶ U // a.cover f}) = ia :=
    Subtype.ext K.middle_spec.symm
  let targetEq : ib = (⟨K.f, homFlattenCover_right J F R φ K.f K.hf⟩ : {f : K.Y ⟶ U // b.cover f}) :=
    Subtype.ext K.middle_spec
  let objA : {f : K.Y ⟶ U // a.cover f} → F.obj (.mk (op K.Y)) :=
    fun f ↦ a.datum.obj (⟨K.Y, f.1, f.2⟩ : a.cover.Arrow)
  let objB : {f : K.Y ⟶ U // b.cover f} → F.obj (.mk (op K.Y)) :=
    fun f ↦ b.datum.obj (⟨K.Y, f.1, f.2⟩ : b.cover.Arrow)
  have sourceValueEq : (restrictDatum J F a.datum (homFlattenCover_left J F R φ)).obj K =
      (restrictDatum J F (pullbackObject J F I.f a).datum raw.left).obj L :=
    congrArg objA sourceEq
  have targetValueEq : (restrictDatum J F (pullbackObject J F I.f b).datum raw.right).obj L =
      (restrictDatum J F b.datum (homFlattenCover_right J F R φ)).obj K :=
    congrArg objB targetEq
  exact eqToHom sourceValueEq ≫ raw.arrow.hom L ≫ eqToHom targetValueEq


/-- The original prestack hypothesis is retained explicitly in the global
commutation law: local equality of original arrows implies equality. -/
theorem homFlattenComponent_comm (hF : F.IsPrestack J)
    {U : C} (R : J.Cover U) {a b : Object J F U}
    (φ : ((presheaf J F).toPseudofunctor'.toDescentData
      (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj a ⟶
      ((presheaf J F).toPseudofunctor'.toDescentData
        (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj b)
    {T : C} (q : T ⟶ U) {I L : (homFlattenCover J F R φ).Arrow}
    (k : T ⟶ I.Y) (l : T ⟶ L.Y) (hk : k ≫ I.f = q) (hl : l ≫ L.f = q) :
    (F.map k.op.toLoc).toFunctor.map (homFlattenComponent J F R φ I) ≫
        (restrictDatum J F b.datum (homFlattenCover_right J F R φ)).hom q k l hk hl =
      (restrictDatum J F a.datum (homFlattenCover_left J F R φ)).hom q k l hk hl ≫
        (F.map l.op.toLoc).toFunctor.map (homFlattenComponent J F R φ L) := sorry

/-- The actual raw amalgamation stores the explicit bound cover and the actual
component maps; the only prestack use is the commutation law above. -/
def homFlatten (hF : F.IsPrestack J) {U : C} (R : J.Cover U) {a b : Object J F U}
    (φ : ((presheaf J F).toPseudofunctor'.toDescentData
      (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj a ⟶
      ((presheaf J F).toPseudofunctor'.toDescentData
        (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj b) : RawHom J F a b where
  cover := homFlattenCover J F R φ
  left := homFlattenCover_left J F R φ
  right := homFlattenCover_right J F R φ
  arrow :=
    { hom := homFlattenComponent J F R φ
      comm := fun {T} q {I L} k l hk hl ↦ homFlattenComponent_comm J F hF R φ q k l hk hl }

/-- Full faithfulness has a concrete quotient-class preimage function. -/
def fullyFaithfulDescent (hF : F.IsPrestack J) {U : C} (R : J.Cover U) :
    ((presheaf J F).toPseudofunctor'.toDescentData
      (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).FullyFaithful where
  preimage φ := _root_.Quotient.mk'' (homFlatten J F hF R φ)
  map_preimage := sorry
  preimage_map := sorry

/-- The category of cover descent objects is a prestack whenever the original
fibre pseudofunctor is a prestack; the new Hom witnesses are the explicit maps. -/
theorem isPrestack (hF : F.IsPrestack J) : (presheaf J F).toPseudofunctor'.IsPrestack J :=
  Pseudofunctor.IsPrestack.of_isPrestackFor fun U R hR ↦
    { nonempty_fullyFaithful := ⟨fullyFaithfulDescent J F hF ⟨R, hR⟩⟩ }

end CategoryTheory.Functor.StackificationConstruction.DescentCompletion
