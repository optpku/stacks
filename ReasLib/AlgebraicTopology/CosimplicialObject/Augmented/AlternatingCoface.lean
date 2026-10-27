/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.NatTrans.Arrow
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Alternating-coface complexes of augmented cosimplicial objects

An augmented cosimplicial object canonically determines a cochain map from its augmentation
point in degree zero to the alternating-coface complex.  This file packages that map naturally
and as a functor to the arrow category, so resolution constructions do not need to rebuild the
degree-zero cocycle condition or its naturality.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.AlternatingCofaceMapComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The coaugmentation of an augmented cosimplicial object is a cocycle in degree zero of its
alternating-coface complex. -/
theorem coaugmentationCocycle (X : CosimplicialObject.Augmented C) :
    X.hom.app (SimplexCategory.mk 0) ≫
      ((alternatingCofaceMapComplex C).obj X.right).d 0 1 = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    have h (i : Fin 2) :
        X.hom.app ⦋0⦌ ≫ X.right.δ i = X.hom.app ⦋1⦌ := by
      have hn : 𝟙 X.left ≫ X.hom.app ⦋1⦌ =
          X.hom.app ⦋0⦌ ≫ X.right.δ i :=
        X.hom.naturality (SimplexCategory.δ i)
      exact hn.symm.trans (Category.id_comp _)
    simp [alternatingCofaceMapComplex, obj, CochainComplex.of.d, objD,
      Fin.sum_univ_two, Preadditive.comp_add, h]

section HasZeroObject

variable [Limits.HasZeroObject C]

/-- The canonical cochain map from the augmentation point in degree zero to the
alternating-coface complex. -/
noncomputable def coaugmentationApp (X : CosimplicialObject.Augmented C) :
    (CochainComplex.single₀ C).obj X.left ⟶
      (alternatingCofaceMapComplex C).obj X.right :=
  (CochainComplex.fromSingle₀Equiv
    ((alternatingCofaceMapComplex C).obj X.right) X.left).symm
      ⟨X.hom.app (SimplexCategory.mk 0), coaugmentationCocycle X⟩

/-- The augmented alternating-coface complex obtained by adjoining the augmentation point in
degree zero. -/
@[stacks 07A1 "extended alternating-coface Cech complex"]
noncomputable def extended (X : CosimplicialObject.Augmented C) :
    CochainComplex C ℕ :=
  CochainComplex.fromSingle₀AsComplex
    ((alternatingCofaceMapComplex C).obj X.right) X.left (coaugmentationApp X)

/-- The augmentation point is the degree-zero object of the extended alternating-coface
complex. -/
@[simp]
theorem extended_X_zero (X : CosimplicialObject.Augmented C) :
    (extended X).X 0 = X.left := rfl

/-- Positive degrees of the extended alternating-coface complex recover the ordinary
alternating-coface complex. -/
@[simp]
theorem extended_X_succ (X : CosimplicialObject.Augmented C) (n : ℕ) :
    (extended X).X (n + 1) = ((alternatingCofaceMapComplex C).obj X.right).X n := rfl

/-- The first differential of the extended alternating-coface complex is the degree-zero
coaugmentation. -/
@[simp]
theorem extended_d_zero_one (X : CosimplicialObject.Augmented C) :
    (extended X).d 0 1 = X.hom.app (SimplexCategory.mk 0) := by
  change (coaugmentationApp X).f 0 = _
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- Positive-degree differentials of the extended complex are the ordinary alternating-coface
differentials. -/
@[simp]
theorem extended_d_succ_succ (X : CosimplicialObject.Augmented C) (i j : ℕ) :
    (extended X).d (i + 1) (j + 1) =
      ((alternatingCofaceMapComplex C).obj X.right).d i j := rfl

/-- The canonical alternating-coface cochain maps are natural in augmented cosimplicial
objects. -/
theorem coaugmentationApp_naturality
    {X Y : CosimplicialObject.Augmented C} (f : X ⟶ Y) :
    (CochainComplex.single₀ C).map f.left ≫ coaugmentationApp Y =
      coaugmentationApp X ≫ (alternatingCofaceMapComplex C).map f.right := by
  set_option backward.isDefEq.respectTransparency false in
    apply HomologicalComplex.from_single_hom_ext
    simpa [coaugmentationApp] using
      (CosimplicialObject.Augmented.w_app (η := f) (n := ⦋0⦌))

/-- The canonical coaugmentation from augmentation points concentrated in degree zero to
alternating-coface complexes. -/
noncomputable def η :
    CosimplicialObject.Augmented.point ⋙ CochainComplex.single₀ C ⟶
      CosimplicialObject.Augmented.drop ⋙ alternatingCofaceMapComplex C where
  app := coaugmentationApp
  naturality := fun _ _ f ↦ coaugmentationApp_naturality f

/-- The degree-zero component of the canonical alternating-coface coaugmentation is the
cosimplicial coaugmentation in degree zero. -/
@[simp]
theorem η_app_f_zero (X : CosimplicialObject.Augmented C) :
    (η.app X).f 0 = X.hom.app (SimplexCategory.mk 0) := by
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- Every positive-degree component of the canonical alternating-coface coaugmentation is
zero. -/
@[simp]
theorem η_app_f_succ (X : CosimplicialObject.Augmented C) (n : ℕ) :
    (η.app X).f (n + 1) = 0 := by
  exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 X.left
    (n + 1) (Nat.succ_ne_zero n)).eq_of_src _ _

/-- The canonical alternating-coface coaugmentation packaged as a functorial family of arrows. -/
noncomputable abbrev arrowFunctor :
    CosimplicialObject.Augmented C ⥤ Arrow (CochainComplex C ℕ) :=
  (η (C := C)).arrowFunctor

/-- The arrow classified by `arrowFunctor` is the canonical alternating-coface
coaugmentation. -/
@[simp]
theorem arrowFunctor_obj_hom (X : CosimplicialObject.Augmented C) :
    (arrowFunctor.obj X).hom = η.app X := rfl

end HasZeroObject

end AlgebraicTopology.AlternatingCofaceMapComplex
