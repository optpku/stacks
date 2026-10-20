/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Binary Biproducts of Filtered Objects

When the ambient category has binary biproducts and zero morphisms, the category of filtered
objects inherits binary biproducts via the stagewise biproduct filtration.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

namespace DecreasingFiltration

variable {X Y : C}

/-- The map from the biproduct of two filtration stages to the biproduct of their ambient
objects. -/
noncomputable abbrev biprodMap (FX : DecreasingFiltration X) (FY : DecreasingFiltration Y)
    (p : ℤ) : ((FX.stage p : C) ⊞ (FY.stage p : C)) ⟶ (X ⊞ Y : C) :=
  Limits.biprod.map (FX.stage p).arrow (FY.stage p).arrow

/-- The stagewise biproduct filtration on `X ⊞ Y`. -/
noncomputable def biprod (FX : DecreasingFiltration X) (FY : DecreasingFiltration Y) :
    DecreasingFiltration (X ⊞ Y : C) where
  toFun p := Subobject.mk (biprodMap FX FY p)
  monotone' := by
    intro p q hpq
    -- `p ≤ q` in `ℤᵒᵈ` means `q ≤ p` in `ℤ`, so stages at `p` are smaller.
    have hX : FX.stage p ≤ FX.stage q := FX.stage_mono (OrderDual.toDual_le_toDual.mp hpq)
    have hY : FY.stage p ≤ FY.stage q := FY.stage_mono (OrderDual.toDual_le_toDual.mp hpq)
    exact Subobject.mk_le_mk_of_comm
      (Limits.biprod.map (Subobject.ofLE _ _ hX) (Subobject.ofLE _ _ hY))
      (by apply Limits.biprod.hom_ext <;> simp [Category.assoc, Subobject.ofLE_arrow])

end DecreasingFiltration

namespace FilteredObject

variable {X Y : FilteredObject C}

/-- The direct sum of two filtered objects, with the biproduct of their stage inclusions as
its filtration. -/
noncomputable def binaryBiproduct (X Y : FilteredObject C) : FilteredObject C where
  obj := X.obj ⊞ Y.obj
  filtration := DecreasingFiltration.biprod X.filtration Y.filtration

/-- The underlying object of the filtered direct sum is the ambient binary biproduct. -/
@[simp]
theorem binaryBiproduct_obj (X Y : FilteredObject C) :
    (binaryBiproduct X Y).obj = (X.obj ⊞ Y.obj) := rfl

/-- The filtration of the filtered direct sum is the stagewise biproduct filtration. -/
@[simp]
theorem binaryBiproduct_filtration (X Y : FilteredObject C) :
    (binaryBiproduct X Y).filtration =
      DecreasingFiltration.biprod X.filtration Y.filtration := rfl

private theorem biprodFst_preserves (X Y : FilteredObject C) (p : ℤ) :
    (X.filtration.stage p).Factors
      (((DecreasingFiltration.biprod X.filtration Y.filtration).stage p).arrow ≫
        biprod.fst) := by
  change (X.filtration.stage p).Factors
    ((Subobject.mk (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).arrow ≫ biprod.fst)
  refine (Subobject.factors_iff _ _).2
    ⟨(Subobject.underlyingIso
      (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫ biprod.fst, ?_⟩
  calc ((Subobject.underlyingIso
      (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫ biprod.fst) ≫
        (X.filtration.stage p).arrow
      = (Subobject.underlyingIso
          (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫
          (biprod.fst ≫ (X.filtration.stage p).arrow) := by
          simp [Category.assoc]
    _ = (Subobject.underlyingIso
        (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫
          (DecreasingFiltration.biprodMap X.filtration Y.filtration p ≫ biprod.fst) := by
      simp [DecreasingFiltration.biprodMap]
    _ = (Subobject.mk (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).arrow ≫
          biprod.fst := by
      simpa only [← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]

private theorem biprodSnd_preserves (X Y : FilteredObject C) (p : ℤ) :
    (Y.filtration.stage p).Factors
      (((DecreasingFiltration.biprod X.filtration Y.filtration).stage p).arrow ≫
        biprod.snd) := by
  change (Y.filtration.stage p).Factors
    ((Subobject.mk (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).arrow ≫ biprod.snd)
  refine (Subobject.factors_iff _ _).2
    ⟨(Subobject.underlyingIso
      (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫ biprod.snd, ?_⟩
  calc ((Subobject.underlyingIso
      (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫ biprod.snd) ≫
        (Y.filtration.stage p).arrow
      = (Subobject.underlyingIso
          (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫
          (biprod.snd ≫ (Y.filtration.stage p).arrow) := by
          simp [Category.assoc]
    _ = (Subobject.underlyingIso
        (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫
          (DecreasingFiltration.biprodMap X.filtration Y.filtration p ≫ biprod.snd) := by
      simp [DecreasingFiltration.biprodMap]
    _ = (Subobject.mk (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).arrow ≫
          biprod.snd := by
      simpa only [← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]

private theorem biprodInl_preserves (X Y : FilteredObject C) (p : ℤ) :
    ((DecreasingFiltration.biprod X.filtration Y.filtration).stage p).Factors
      ((X.filtration.stage p).arrow ≫ biprod.inl) := by
  change (Subobject.mk (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).Factors
    ((X.filtration.stage p).arrow ≫ biprod.inl)
  rw [Subobject.mk_factors_iff]
  exact ⟨biprod.inl, by simp [DecreasingFiltration.biprodMap]⟩

private theorem biprodInr_preserves (X Y : FilteredObject C) (p : ℤ) :
    ((DecreasingFiltration.biprod X.filtration Y.filtration).stage p).Factors
      ((Y.filtration.stage p).arrow ≫ biprod.inr) := by
  change (Subobject.mk (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).Factors
    ((Y.filtration.stage p).arrow ≫ biprod.inr)
  rw [Subobject.mk_factors_iff]
  exact ⟨biprod.inr, by simp [DecreasingFiltration.biprodMap]⟩

private theorem biprodLift_preserves {W : FilteredObject C} (f : W ⟶ X) (g : W ⟶ Y) (p : ℤ) :
    ((DecreasingFiltration.biprod X.filtration Y.filtration).stage p).Factors
      ((W.filtration.stage p).arrow ≫ biprod.lift f.hom g.hom) := by
  change (Subobject.mk (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).Factors
    ((W.filtration.stage p).arrow ≫ biprod.lift f.hom g.hom)
  rw [Subobject.mk_factors_iff]
  exact ⟨biprod.lift (Hom.stageMap f p) (Hom.stageMap g p),
    by apply biprod.hom_ext <;> simp [DecreasingFiltration.biprodMap, Category.assoc]⟩

private theorem biprodDesc_preserves {Z : FilteredObject C} (f : X ⟶ Z) (g : Y ⟶ Z) (p : ℤ) :
    (Z.filtration.stage p).Factors
      (((DecreasingFiltration.biprod X.filtration Y.filtration).stage p).arrow ≫
        biprod.desc f.hom g.hom) := by
  change (Z.filtration.stage p).Factors
    ((Subobject.mk (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).arrow ≫
      biprod.desc f.hom g.hom)
  refine (Subobject.factors_iff _ _).2
    ⟨(Subobject.underlyingIso
      (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫
      biprod.desc (Hom.stageMap f p) (Hom.stageMap g p), ?_⟩
  calc ((Subobject.underlyingIso
      (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫
        biprod.desc (Hom.stageMap f p) (Hom.stageMap g p)) ≫ (Z.filtration.stage p).arrow
      = (Subobject.underlyingIso
          (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫
          (biprod.desc (Hom.stageMap f p) (Hom.stageMap g p) ≫ (Z.filtration.stage p).arrow) := by
          simp [Category.assoc]
    _ = (Subobject.underlyingIso
        (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).hom ≫
          (DecreasingFiltration.biprodMap X.filtration Y.filtration p ≫ biprod.desc f.hom g.hom) := by
      congr 1
      apply biprod.hom_ext'
      all_goals simp [DecreasingFiltration.biprodMap]
    _ = (Subobject.mk (DecreasingFiltration.biprodMap X.filtration Y.filtration p)).arrow ≫
          biprod.desc f.hom g.hom := by simp

private noncomputable def binaryBicone (X Y : FilteredObject C) : BinaryBicone X Y where
  pt := binaryBiproduct X Y
  fst := { hom := biprod.fst, preserves := biprodFst_preserves X Y }
  snd := { hom := biprod.snd, preserves := biprodSnd_preserves X Y }
  inl := { hom := biprod.inl, preserves := biprodInl_preserves X Y }
  inr := { hom := biprod.inr, preserves := biprodInr_preserves X Y }
  inl_fst := by
    apply FilteredObject.forget.map_injective; change biprod.inl ≫ biprod.fst = 𝟙 X.obj
    exact biprod.inl_fst
  inl_snd := by
    apply FilteredObject.forget.map_injective; change biprod.inl ≫ biprod.snd = 0
    exact biprod.inl_snd
  inr_fst := by
    apply FilteredObject.forget.map_injective; change biprod.inr ≫ biprod.fst = 0
    exact biprod.inr_fst
  inr_snd := by
    apply FilteredObject.forget.map_injective; change biprod.inr ≫ biprod.snd = 𝟙 Y.obj
    exact biprod.inr_snd

private noncomputable def binaryBiconeIsBilimit (X Y : FilteredObject C) :
    (binaryBicone X Y).IsBilimit where
  isLimit :=
    { lift := fun s ↦
        { hom := biprod.lift (BinaryFan.fst s).hom (BinaryFan.snd s).hom
          preserves := biprodLift_preserves (BinaryFan.fst s) (BinaryFan.snd s) }
      fac := by
        intro s j; rcases j with ⟨⟨⟩⟩
        · apply FilteredObject.forget.map_injective
          exact biprod.lift_fst (BinaryFan.fst s).hom (BinaryFan.snd s).hom
        · apply FilteredObject.forget.map_injective
          exact biprod.lift_snd (BinaryFan.fst s).hom (BinaryFan.snd s).hom
      uniq := by
        intro s m h; apply FilteredObject.forget.map_injective
        apply biprod.hom_ext
        · change m.hom ≫ biprod.fst = biprod.lift _ _ ≫ biprod.fst
          rw [biprod.lift_fst]
          have condition := congrArg Hom.hom (h ⟨WalkingPair.left⟩)
          change m.hom ≫ biprod.fst = (BinaryFan.fst s).hom at condition
          exact condition
        · change m.hom ≫ biprod.snd = biprod.lift _ _ ≫ biprod.snd
          rw [biprod.lift_snd]
          have condition := congrArg Hom.hom (h ⟨WalkingPair.right⟩)
          change m.hom ≫ biprod.snd = (BinaryFan.snd s).hom at condition
          exact condition }
  isColimit :=
    { desc := fun s ↦
        { hom := biprod.desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom
          preserves := biprodDesc_preserves (BinaryCofan.inl s) (BinaryCofan.inr s) }
      fac := by
        intro s j; rcases j with ⟨⟨⟩⟩
        · apply FilteredObject.forget.map_injective
          exact biprod.inl_desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom
        · apply FilteredObject.forget.map_injective
          exact biprod.inr_desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom
      uniq := by
        intro s m h; apply FilteredObject.forget.map_injective
        apply biprod.hom_ext'
        · change biprod.inl ≫ m.hom = biprod.inl ≫ biprod.desc _ _
          rw [biprod.inl_desc]
          have condition := congrArg Hom.hom (h ⟨WalkingPair.left⟩)
          change biprod.inl ≫ m.hom = (BinaryCofan.inl s).hom at condition
          exact condition
        · change biprod.inr ≫ m.hom = biprod.inr ≫ biprod.desc _ _
          rw [biprod.inr_desc]
          have condition := congrArg Hom.hom (h ⟨WalkingPair.right⟩)
          change biprod.inr ≫ m.hom = (BinaryCofan.inr s).hom at condition
          exact condition }

/-- The stagewise direct sum is a binary biproduct of the two filtered objects. -/
noncomputable instance instHasBinaryBiproduct (X Y : FilteredObject C) :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := binaryBicone X Y
      isBilimit := binaryBiconeIsBilimit X Y }

/-- The binary biproduct structure on filtered objects is given by the stagewise biproduct
filtration. -/
@[reducible] noncomputable def hasBinaryBiproduct (X Y : FilteredObject C) : HasBinaryBiproduct X Y :=
  instHasBinaryBiproduct X Y

/-- Filtered objects inherit all binary biproducts from the stagewise construction. -/
noncomputable instance instHasBinaryBiproducts : HasBinaryBiproducts (FilteredObject C) where
  has_binary_biproduct X Y := hasBinaryBiproduct X Y

end FilteredObject

end CategoryTheory
