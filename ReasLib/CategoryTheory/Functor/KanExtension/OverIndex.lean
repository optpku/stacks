/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u v u' v'
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) (V : C) (U : Over (F.obj V))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Forget the slice structure in the pointwise inverse-image Kan index. -/
def overKanForget :
    CostructuredArrow (Over.post F).op (op U) ⥤ CostructuredArrow F.op (op U.left) where
  obj a := CostructuredArrow.mk (S := F.op) (Y := op a.left.unop.left) a.hom.unop.left.op
  map a := CostructuredArrow.homMk a.left.unop.left.op (by
    apply Quiver.Hom.unop_inj
    simpa [Over.post] using congrArg (fun f ↦ f.unop.left) (CostructuredArrow.w a))
  map_id a := by
    apply CostructuredArrow.hom_ext
    rfl
  map_comp a b := by
    apply CostructuredArrow.hom_ext
    rfl

variable [HasBinaryProducts C] [HasBinaryProducts D]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Refine a Kan chart by the fixed slice object using an actual product. -/
def overKanRefine :
    CostructuredArrow F.op (op U.left) ⥤ CostructuredArrow (Over.post F).op (op U) where
  obj a :=
    CostructuredArrow.mk (S := (Over.post F).op)
      (Over.homMk (V := (Over.post F).obj (Over.mk
        (prod.snd : a.left.unop ⨯ V ⟶ V)))
        (prod.lift a.hom.unop U.hom ≫ (PreservesLimitPair.iso F a.left.unop V).inv)
        (by simp [Over.post])).op
  map {a b} f := CostructuredArrow.homMk
    (Over.homMk (prod.map f.left.unop (𝟙 V)) (by
      change prod.map f.left.unop (𝟙 V) ≫ prod.snd = prod.snd
      simp)).op (by
      apply Quiver.Hom.unop_inj
      apply Over.OverMorphism.ext
      change (prod.lift b.hom.unop U.hom ≫
          (PreservesLimitPair.iso F b.left.unop V).inv) ≫
          F.map (prod.map f.left.unop (𝟙 V)) =
        prod.lift a.hom.unop U.hom ≫ (PreservesLimitPair.iso F a.left.unop V).inv
      apply BinaryFan.IsLimit.hom_ext (isLimitOfHasBinaryProductOfPreservesLimit F _ V)
      · change _ ≫ F.map prod.fst = _ ≫ F.map prod.fst
        simp only [Category.assoc]
        rw [← F.map_comp, prod.map_fst, F.map_comp]
        have hw := congrArg Quiver.Hom.unop (CostructuredArrow.w f)
        change b.hom.unop ≫ F.map f.left.unop = a.hom.unop at hw
        simp only [PreservesLimitPair.iso_inv_fst_assoc,
          PreservesLimitPair.iso_inv_fst, prod.lift_fst]
        exact (prod.lift_fst_assoc b.hom.unop U.hom (F.map f.left.unop)).trans hw
      · change _ ≫ F.map prod.snd = _ ≫ F.map prod.snd
        simp only [Category.assoc]
        rw [← F.map_comp, prod.map_snd, F.map_comp]
        simp only [map_id, Category.comp_id, PreservesLimitPair.iso_inv_snd]
        exact (prod.lift_snd b.hom.unop U.hom).trans (prod.lift_snd a.hom.unop U.hom).symm)
  map_id a := by
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    simp
  map_comp a b := by
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Product refinement is left adjoint to forgetting the slice structure. -/
def overKanAdjunction : overKanRefine F V U ⊣ overKanForget F V U :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun a b ↦
        { toFun := fun h ↦ CostructuredArrow.homMk
            (h.left.unop.left ≫ (prod.fst : a.left.unop ⨯ V ⟶ a.left.unop)).op (by
              apply Quiver.Hom.unop_inj
              have hw := congrArg (fun f ↦ f.unop.left) (CostructuredArrow.w h)
              change b.hom.unop.left ≫ F.map h.left.unop.left =
                prod.lift a.hom.unop U.hom ≫
                  (PreservesLimitPair.iso F a.left.unop V).inv at hw
              change b.hom.unop.left ≫ F.map (h.left.unop.left ≫ prod.fst) = a.hom.unop
              rw [F.map_comp, ← Category.assoc, hw]
              simp only [Category.assoc, PreservesLimitPair.iso_inv_fst, prod.lift_fst])
          invFun := fun h ↦ CostructuredArrow.homMk
            (Over.homMk (prod.lift h.left.unop b.left.unop.hom) (by
              change prod.lift h.left.unop b.left.unop.hom ≫ prod.snd = b.left.unop.hom
              exact prod.lift_snd _ _)).op (by
              apply Quiver.Hom.unop_inj
              apply Over.OverMorphism.ext
              change b.hom.unop.left ≫ F.map (prod.lift h.left.unop b.left.unop.hom) =
                prod.lift a.hom.unop U.hom ≫ (PreservesLimitPair.iso F a.left.unop V).inv
              apply BinaryFan.IsLimit.hom_ext
                (isLimitOfHasBinaryProductOfPreservesLimit F a.left.unop V)
              · change _ ≫ F.map prod.fst = _ ≫ F.map prod.fst
                simp only [Category.assoc]
                rw [← F.map_comp, prod.lift_fst]
                simp only [PreservesLimitPair.iso_inv_fst, prod.lift_fst]
                exact congrArg Quiver.Hom.unop (CostructuredArrow.w h)
              · change _ ≫ F.map prod.snd = _ ≫ F.map prod.snd
                simp only [Category.assoc]
                rw [← F.map_comp, prod.lift_snd]
                simp only [PreservesLimitPair.iso_inv_snd]
                exact (Over.w b.hom.unop).trans (prod.lift_snd a.hom.unop U.hom).symm)
          left_inv := fun h ↦ by
            apply CostructuredArrow.hom_ext
            apply Quiver.Hom.unop_inj
            apply Over.OverMorphism.ext
            change prod.lift (h.left.unop.left ≫ prod.fst) b.left.unop.hom = h.left.unop.left
            apply prod.hom_ext
            · simp
            · rw [prod.lift_snd]
              have hw := Over.w h.left.unop
              change h.left.unop.left ≫ prod.snd = b.left.unop.hom at hw
              exact hw.symm
          right_inv := fun h ↦ by
            apply CostructuredArrow.hom_ext
            apply Quiver.Hom.unop_inj
            simp }
      homEquiv_naturality_left_symm := by
        intro a' a b f h
        apply CostructuredArrow.hom_ext
        apply Quiver.Hom.unop_inj
        apply Over.OverMorphism.ext
        change prod.lift (h.left.unop ≫ f.left.unop) b.left.unop.hom =
          prod.lift h.left.unop b.left.unop.hom ≫ prod.map f.left.unop (𝟙 V)
        simp
      homEquiv_naturality_right := by
        intro a b b' f h
        apply CostructuredArrow.hom_ext
        apply Quiver.Hom.unop_inj
        change (h.left.unop.left ≫ f.left.unop.left) ≫ prod.fst =
          h.left.unop.left ≫ f.left.unop.left ≫ prod.fst
        exact Category.assoc _ _ _ }

instance overKanForget_final : (overKanForget F V U).Final :=
  final_of_adjunction (overKanAdjunction F V U)

variable {A : Type*} [Category* A] (P : Cᵒᵖ ⥤ A)
variable [F.op.HasLeftKanExtension P] [F.op.HasPointwiseLeftKanExtension P]
variable [(Over.post F).op.HasLeftKanExtension ((Over.forget V).op ⋙ P)]
variable [(Over.post F).op.HasPointwiseLeftKanExtension ((Over.forget V).op ⋙ P)]

/-- The slice Kan extension uses the same colimit, through the actual final forgetful index. -/
def overKanObjIso :
    ((Over.post F).op.leftKanExtension ((Over.forget V).op ⋙ P)).obj (op U) ≅
      (F.op.leftKanExtension P).obj (op U.left) :=
  ((Over.post F).op.leftKanExtensionObjIsoColimit ((Over.forget V).op ⋙ P) (op U)) ≪≫
    (Final.colimitIso (overKanForget F V U)
      (CostructuredArrow.proj F.op (op U.left) ⋙ P)) ≪≫
    (F.op.leftKanExtensionObjIsoColimit P (op U.left)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison sends each slice Kan chart to its underlying Kan chart. -/
@[reassoc]
lemma overKanObjIso_hom_fac (a : CostructuredArrow (Over.post F).op (op U)) :
    ((Over.post F).op.leftKanExtensionUnit ((Over.forget V).op ⋙ P)).app a.left ≫
      ((Over.post F).op.leftKanExtension ((Over.forget V).op ⋙ P)).map a.hom ≫
      (overKanObjIso F V U P).hom =
    (F.op.leftKanExtensionUnit P).app (op a.left.unop.left) ≫
      (F.op.leftKanExtension P).map a.hom.unop.left.op := by
  simp only [overKanObjIso, Iso.trans_hom, Iso.symm_hom]
  rw [ι_leftKanExtensionObjIsoColimit_hom_assoc (Over.post F).op
    ((Over.forget V).op ⋙ P) (op U) a]
  calc
    _ = colimit.ι (CostructuredArrow.proj F.op (op U.left) ⋙ P)
        ((overKanForget F V U).obj a) ≫
        (F.op.leftKanExtensionObjIsoColimit P (op U.left)).inv :=
      Final.ι_colimitIso_hom_assoc (overKanForget F V U)
        (CostructuredArrow.proj F.op (op U.left) ⋙ P) a _
    _ = _ := ι_leftKanExtensionObjIsoColimit_inv F.op P (op U.left)
      ((overKanForget F V U).obj a)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual pointwise colimit comparisons form the slice Kan comparison. -/
def overKanIso :
    (Over.post F).op.leftKanExtension ((Over.forget V).op ⋙ P) ≅
      (Over.forget (F.obj V)).op ⋙ F.op.leftKanExtension P :=
  NatIso.ofComponents (fun U ↦ overKanObjIso F V U.unop P) (by
    intro X Y f
    apply (isPointwiseLeftKanExtensionLeftKanExtensionUnit (Over.post F).op
      ((Over.forget V).op ⋙ P) X).hom_ext'
    intro W φ
    change ((Over.post F).op.leftKanExtensionUnit ((Over.forget V).op ⋙ P)).app W ≫
        ((Over.post F).op.leftKanExtension ((Over.forget V).op ⋙ P)).map φ ≫
        (((Over.post F).op.leftKanExtension ((Over.forget V).op ⋙ P)).map f ≫
          (overKanObjIso F V Y.unop P).hom) =
      ((Over.post F).op.leftKanExtensionUnit ((Over.forget V).op ⋙ P)).app W ≫
        ((Over.post F).op.leftKanExtension ((Over.forget V).op ⋙ P)).map φ ≫
        ((overKanObjIso F V X.unop P).hom ≫
          (F.op.leftKanExtension P).map f.unop.left.op)
    calc
      _ = ((Over.post F).op.leftKanExtensionUnit ((Over.forget V).op ⋙ P)).app W ≫
          ((Over.post F).op.leftKanExtension ((Over.forget V).op ⋙ P)).map (φ ≫ f) ≫
          (overKanObjIso F V Y.unop P).hom := by
        simp only [map_comp, Category.assoc]
      _ = (F.op.leftKanExtensionUnit P).app (op W.unop.left) ≫
          (F.op.leftKanExtension P).map (φ ≫ f).unop.left.op :=
        overKanObjIso_hom_fac F V Y.unop P (CostructuredArrow.mk (φ ≫ f))
      _ = ((F.op.leftKanExtensionUnit P).app (op W.unop.left) ≫
          (F.op.leftKanExtension P).map φ.unop.left.op) ≫
          (F.op.leftKanExtension P).map f.unop.left.op := by
        simp only [unop_comp, Over.comp_left, op_comp, map_comp, Category.assoc]
      _ = _ := by
        simpa only [CostructuredArrow.mk_left, CostructuredArrow.mk_hom_eq_self,
          Category.assoc] using
          congrArg (fun k ↦ k ≫ (F.op.leftKanExtension P).map f.unop.left.op)
            (overKanObjIso_hom_fac F V X.unop P (CostructuredArrow.mk φ)).symm)

end CategoryTheory.Functor
