/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Biproduct
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.FinitePreadditive
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Binary Biproducts of Finite Filtered Objects

This leaf records the closure facts that let Mathlib lift binary products from filtered objects to
the full subcategory of finite filtrations. The resulting biproducts are canonical full-subcategory
constructions, rather than a second hand-built additive presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C] [HasZeroObject C]

/-- Isomorphisms of filtered objects carry each stage to the corresponding stage. -/
theorem stage_map_iso {X Y : FilteredObject C} (e : X ≅ Y) (p : ℤ) :
    (Subobject.mapIsoToOrderIso (forget.mapIso e)) (X.filtration.stage p) =
      Y.filtration.stage p := by
  let E := forget.mapIso e
  have hf {A B : FilteredObject C} (e : A ≅ B) :
      (Subobject.map (forget.mapIso e).hom).obj (A.filtration.stage p) ≤
        B.filtration.stage p := by
    letI : IsIso e.hom.hom := (forget.mapIso e).isIso_hom
    change (Subobject.map e.hom.hom).obj _ ≤ _
    conv_lhs => rw [← Subobject.mk_arrow (A.filtration.stage p)]
    erw [Subobject.map_mk]
    exact Subobject.mk_le_of_comm (e.hom.stageMap p) (Hom.stageMap_arrow e.hom p)
  refine le_antisymm (hf e) ?_
  have h := (Subobject.mapIsoToOrderIso E).monotone (hf e.symm)
  change (Subobject.map E.hom).obj
    ((Subobject.map E.inv).obj (Y.filtration.stage p)) ≤ _ at h
  simpa only [← Subobject.map_comp, E.inv_hom_id, Subobject.map_id] using h

namespace IsFinite

/-- Finite filtrations are invariant under isomorphism of filtered objects. -/
@[stacks 05S1 "finite filtered biproducts"]
instance closedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsFinite : ObjectProperty (FilteredObject C)) where
  of_iso {X Y} e hX := by
    obtain ⟨a, b, ha, hb⟩ := hX
    refine ⟨a, b, ?_, ?_⟩
    · rw [← stage_map_iso e a, ha]
      exact (Subobject.mapIsoToOrderIso (forget.mapIso e)).map_top
    · rw [← stage_map_iso e b, hb]
      exact (Subobject.mapIsoToOrderIso (forget.mapIso e)).map_bot

/-- The stagewise biproduct has the minimum of the lower bounds and the maximum
of the upper bounds of its two input filtrations. -/
theorem binaryBiproduct [Preadditive C] [HasBinaryBiproducts C]
    {X Y : FilteredObject C} (hX : IsFinite X) (hY : IsFinite Y) :
    IsFinite (FilteredObject.binaryBiproduct X Y) := by
  obtain ⟨a, b, ha, hb⟩ := hX
  obtain ⟨c, d, hc, hd⟩ := hY
  have hXa : X.filtration.stage (min a c) = ⊤ :=
    top_unique (ha ▸ X.filtration.stage_mono (min_le_left a c))
  have hYa : Y.filtration.stage (min a c) = ⊤ :=
    top_unique (hc ▸ Y.filtration.stage_mono (min_le_right a c))
  have hXb : X.filtration.stage (max b d) = ⊥ :=
    bot_unique (hb ▸ X.filtration.stage_mono (le_max_left b d))
  have hYb : Y.filtration.stage (max b d) = ⊥ :=
    bot_unique (hd ▸ Y.filtration.stage_mono (le_max_right b d))
  refine ⟨min a c, max b d, ?_, ?_⟩
  · change Subobject.mk (DecreasingFiltration.biprodMap
      X.filtration Y.filtration (min a c)) = ⊤
    dsimp only [DecreasingFiltration.biprodMap]
    letI : IsIso (X.filtration.stage (min a c)).arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr hXa
    letI : IsIso (Y.filtration.stage (min a c)).arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr hYa
    letI : IsIso (biprod.map (X.filtration.stage (min a c)).arrow
        (Y.filtration.stage (min a c)).arrow) := (biprod.mapIso (asIso (X.filtration.stage (min a c)).arrow)
      (asIso (Y.filtration.stage (min a c)).arrow)).isIso_hom
    exact Subobject.mk_eq_top_of_isIso _
  · change Subobject.mk (DecreasingFiltration.biprodMap
      X.filtration Y.filtration (max b d)) = ⊥
    apply Subobject.mk_eq_bot_iff_zero.mpr
    change biprod.map (X.filtration.stage (max b d)).arrow
      (Y.filtration.stage (max b d)).arrow = 0
    rw [hXb, hYb, Subobject.bot_arrow, Subobject.bot_arrow]
    ext <;> simp

end IsFinite

namespace Finite

/-- The actual binary product cone on the existing stagewise biproduct model. -/
def binaryBiproductFan [Preadditive C] [HasBinaryBiproducts C]
    (X Y : FilteredObject C) : BinaryFan X Y :=
  BinaryFan.mk
    (Hom.mk (X := FilteredObject.binaryBiproduct X Y) (Y := X)
      (biprod.fst : X.obj ⊞ Y.obj ⟶ X.obj) (fun p ↦ by
        apply (Subobject.factors_iff _ _).mpr
        refine ⟨(Subobject.underlyingIso (DecreasingFiltration.biprodMap
          X.filtration Y.filtration p)).hom ≫ biprod.fst, ?_⟩
        calc
          (_ ≫ biprod.fst) ≫ (
              X.filtration.stage p).arrow =
              (Subobject.underlyingIso (DecreasingFiltration.biprodMap
                X.filtration Y.filtration p)).hom ≫
                  (biprod.fst ≫ (X.filtration.stage p).arrow) := by simp [Category.assoc]
          _ = (Subobject.underlyingIso (DecreasingFiltration.biprodMap
                X.filtration Y.filtration p)).hom ≫
                  (DecreasingFiltration.biprodMap X.filtration Y.filtration p ≫ biprod.fst) := by
                simp [DecreasingFiltration.biprodMap]
          _ = (Subobject.mk (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).arrow ≫
                biprod.fst := by
                simpa only [← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]))
    (Hom.mk (X := FilteredObject.binaryBiproduct X Y) (Y := Y)
      (biprod.snd : X.obj ⊞ Y.obj ⟶ Y.obj) (fun p ↦ by
        apply (Subobject.factors_iff _ _).mpr
        refine ⟨(Subobject.underlyingIso (DecreasingFiltration.biprodMap
          X.filtration Y.filtration p)).hom ≫ biprod.snd, ?_⟩
        calc
          (_ ≫ biprod.snd) ≫ (
              Y.filtration.stage p).arrow =
              (Subobject.underlyingIso (DecreasingFiltration.biprodMap
                X.filtration Y.filtration p)).hom ≫
                  (biprod.snd ≫ (Y.filtration.stage p).arrow) := by simp [Category.assoc]
          _ = (Subobject.underlyingIso (DecreasingFiltration.biprodMap
                X.filtration Y.filtration p)).hom ≫
                  (DecreasingFiltration.biprodMap X.filtration Y.filtration p ≫ biprod.snd) := by
                simp [DecreasingFiltration.biprodMap]
          _ = (Subobject.mk (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).arrow ≫
                biprod.snd := by
                simpa only [← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]))

/-- The explicit fan satisfies the binary product universal property. -/
def binaryBiproductFanIsLimit [Preadditive C] [HasBinaryBiproducts C]
    (X Y : FilteredObject C) : IsLimit (binaryBiproductFan X Y) := by
  refine BinaryFan.IsLimit.mk _ (fun f g ↦ Hom.mk (Y := FilteredObject.binaryBiproduct X Y) (biprod.lift f.hom g.hom)
    (fun p ↦ ?_)) ?_ ?_ ?_
  · change (Subobject.mk (DecreasingFiltration.biprodMap
      X.filtration Y.filtration p)).Factors _
    rw [Subobject.mk_factors_iff]
    exact ⟨biprod.lift (f.stageMap p) (g.stageMap p), by
      apply biprod.hom_ext <;> simp [DecreasingFiltration.biprodMap, Category.assoc]⟩
  · intro W f g
    apply Hom.ext
    exact biprod.lift_fst _ _
  · intro W f g
    apply Hom.ext
    exact biprod.lift_snd _ _
  · intro W f g m hf hg
    apply Hom.ext
    apply biprod.hom_ext
    · exact (congrArg Hom.hom hf).trans (biprod.lift_fst _ _).symm
    · exact (congrArg Hom.hom hg).trans (biprod.lift_snd _ _).symm

end Finite

namespace IsFinite

/-- Finite filtrations are closed under binary products of filtered objects. -/
@[stacks 05S1 "finite filtered biproducts"]
instance closedUnderBinaryProducts
    [Preadditive C] [HasBinaryBiproducts C] :
    ObjectProperty.IsClosedUnderBinaryProducts
      (IsFinite : ObjectProperty (FilteredObject C)) :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (fun Z h ↦ by
    obtain ⟨F, hF⟩ := h
    let X := F.obj ⟨WalkingPair.left⟩
    let Y := F.obj ⟨WalkingPair.right⟩
    let e : limit F ≅ FilteredObject.binaryBiproduct X Y :=
      HasLimit.isoOfNatIso (diagramIsoPair F) ≪≫
        limit.isoLimitCone ⟨_, Finite.binaryBiproductFanIsLimit X Y⟩
    exact (ObjectProperty.prop_iff_of_iso
      (IsFinite : ObjectProperty (FilteredObject C)) e).mpr
        (binaryBiproduct (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))

end IsFinite

namespace Finite

/-- Finite filtered objects inherit binary products from filtered objects. -/
@[stacks 05S1 "finite filtered biproducts"]
noncomputable instance hasBinaryProducts
    [Preadditive C] [HasBinaryBiproducts C] :
    HasBinaryProducts (FilteredObject.Finite.category C) :=
  inferInstance

/-- Finite filtered objects inherit binary biproducts from their canonical preadditive and
binary-product structures. -/
@[stacks 05S1 "finite filtered biproducts"]
noncomputable instance hasBinaryBiproducts
    [Preadditive C] [HasBinaryBiproducts C] :
    HasBinaryBiproducts (FilteredObject.Finite.category C) :=
  HasBinaryBiproducts.of_hasBinaryProducts

end Finite

end CategoryTheory.FilteredObject
