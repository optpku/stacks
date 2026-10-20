/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Graded
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped DirectSum

noncomputable section

universe w v u

namespace CategoryTheory

section

variable (C : Type u) [Category.{v} C]

/-- Remark 22.25.7 (09P3): if `C` has shifts by `ℤ`, then `Cᵍʳ` is the category with the same
objects as `C` and total Hom from `X` to `Y` given by `⨁ n : ℤ, ShiftedHom X Y n`. With a
compatible linear structure, these summands define the canonical grading on `Cᵍʳ`. -/
@[stacks 09P3]
structure ShiftedHomCategory where
  /-- The object of the original category underlying a shifted-Hom category object. -/
  obj : C

namespace ShiftedHomCategory

/-- The category whose morphisms are direct sums of shifted morphisms in `C`. -/
scoped notation:max C:max "ᵍʳ" => ShiftedHomCategory C

/-- A shifted-Hom category object coerces to its underlying object. -/
instance instCoe : CoeTC (Cᵍʳ) C where
  coe X := X.obj

/-- Regard an object of `C` as an object of its shifted-Hom category. -/
def of (X : C) : Cᵍʳ :=
  ⟨X⟩

/-- Coercing a shifted-Hom category object built from `X` returns `X`. -/
@[simp] theorem coe_mk (X : C) : ((⟨X⟩ : Cᵍʳ) : C) = X := sorry

/-- Coercing `of C X` to `C` returns `X`. -/
@[simp] theorem coe_of (X : C) : (of C X : C) = X := sorry

section Basic

open scoped ShiftedHomCategory

variable [Preadditive C] [HasShift C ℤ]

/-- The homogeneous degree-`n` morphisms in `Cᵍʳ`. -/
abbrev shiftedHom (X Y : Cᵍʳ) (n : ℤ) : Type v :=
  ShiftedHom (X : C) (Y : C) n

/-- The total Hom in `Cᵍʳ` is the direct sum of the shifted-Hom groups. -/
@[stacks 09P3]
abbrev homSpace (X Y : Cᵍʳ) :=
  ⨁ n : ℤ, ShiftedHom (X : C) (Y : C) n

/-- `homSpace` is definitionally the direct sum of the shifted-Hom groups. -/
theorem homSpace_def (X Y : Cᵍʳ) :
    homSpace C X Y = ⨁ n : ℤ, ShiftedHom (X : C) (Y : C) n := sorry

/-- The degree-zero identity in `Cᵍʳ`, viewed as a shifted morphism. -/
def idHom (X : Cᵍʳ) : ShiftedHom (X : C) (X : C) (0 : ℤ) :=
  ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (X : C))

/-- The identity morphism in `Cᵍʳ`, concentrated in degree zero. -/
def idSpace (X : Cᵍʳ) : homSpace C X X :=
  DirectSum.of (fun n ↦ shiftedHom C X X n) 0 (idHom C X)

/-- Composition of degree-`n` and degree-`m` shifted morphisms, in degree `n + m`. -/
@[stacks 09P3]
abbrev compHomDegree {X Y Z : Cᵍʳ} {m n : ℤ}
    (g : ShiftedHom (Y : C) (Z : C) m) (f : ShiftedHom (X : C) (Y : C) n) :
    ShiftedHom (X : C) (Z : C) (n + m) :=
  ShiftedHom.comp f g (add_comm m n)

/-- `compHomDegree` is the `n + m` specialization of `ShiftedHom.comp`. -/
theorem compHomDegree_def {X Y Z : Cᵍʳ} {m n : ℤ}
    (g : ShiftedHom (Y : C) (Z : C) m) (f : ShiftedHom (X : C) (Y : C) n) :
    compHomDegree C g f = ShiftedHom.comp f g (add_comm m n) := sorry

/-- Homogeneous composition is additive in its left input. -/
@[simp] theorem compHomDegree_add_left
    [h_shift_additive : ∀ n : ℤ, (shiftFunctor C n).Additive]
    {X Y Z : Cᵍʳ} {m n : ℤ}
    (g₁ g₂ : ShiftedHom (Y : C) (Z : C) m) (f : ShiftedHom (X : C) (Y : C) n) :
    compHomDegree C (g₁ + g₂) f = compHomDegree C g₁ f + compHomDegree C g₂ f := sorry

/-- Homogeneous composition is additive in its right input. -/
@[simp] theorem compHomDegree_add_right {X Y Z : Cᵍʳ} {m n : ℤ}
    (g : ShiftedHom (Y : C) (Z : C) m) (f₁ f₂ : ShiftedHom (X : C) (Y : C) n) :
    compHomDegree C g (f₁ + f₂) = compHomDegree C g f₁ + compHomDegree C g f₂ := sorry

/-- Homogeneous composition commutes with integer scalars in its left input. -/
@[simp] theorem compHomDegree_smul_left
    [h_shift_additive : ∀ n : ℤ, (shiftFunctor C n).Additive]
    {X Y Z : Cᵍʳ} {m n : ℤ}
    (r : ℤ) (g : ShiftedHom (Y : C) (Z : C) m) (f : ShiftedHom (X : C) (Y : C) n) :
    compHomDegree C (r • g) f = r • compHomDegree C g f := sorry

/-- Homogeneous composition commutes with integer scalars in its right input. -/
@[simp] theorem compHomDegree_smul_right {X Y Z : Cᵍʳ} {m n : ℤ}
    (r : ℤ) (g : ShiftedHom (Y : C) (Z : C) m) (f : ShiftedHom (X : C) (Y : C) n) :
    compHomDegree C g (r • f) = r • compHomDegree C g f := sorry

/-- Composition by a fixed homogeneous morphism as an integer-linear map. -/
def compHomLinear {X Y Z : Cᵍʳ} {m n : ℤ} (g : shiftedHom C X Y m) :
    shiftedHom C Z X n →ₗ[ℤ] shiftedHom C Z Y (n + m) where
  toFun := compHomDegree C g
  map_add' := sorry
  map_smul' := sorry

/-- Postcomposition by a homogeneous morphism on the total shifted-Hom space. -/
def postcomposeHom {X Y Z : Cᵍʳ} {m : ℤ} (g : shiftedHom C Y Z m) :
    homSpace C X Y →ₗ[ℤ] homSpace C X Z :=
  DirectSum.toModule ℤ ℤ (homSpace C X Z)
    (fun n ↦ (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom C X Z i) (n + m)).comp
      (compHomLinear C g))

/-- Postcomposition, linear in a fixed homogeneous degree. -/
def composeByDegree [h_shift_additive : ∀ n : ℤ, (shiftFunctor C n).Additive]
    {X Y Z : Cᵍʳ} (m : ℤ) :
    shiftedHom C Y Z m →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z where
  toFun := postcomposeHom C
  map_add' := sorry
  map_smul' := sorry

section Composition

variable [shift_additive : ∀ n : ℤ, (shiftFunctor C n).Additive]

/-- Composition on total shifted-Hom spaces as a curried bilinear map. -/
def compLinear {X Y Z : Cᵍʳ} :
    homSpace C Y Z →ₗ[ℤ] homSpace C X Y →ₗ[ℤ] homSpace C X Z :=
  DirectSum.toModule ℤ ℤ (homSpace C X Y →ₗ[ℤ] homSpace C X Z) (composeByDegree C)

/-- Composition in `Cᵍʳ`, induced by homogeneous shifted-Hom composition. -/
def compSpace {X Y Z : Cᵍʳ} (g : homSpace C Y Z) (f : homSpace C X Y) :
    homSpace C X Z :=
  compLinear C g f

/-- Composition on `DirectSum.lof` generators is homogeneous composition. -/
@[simp] theorem compSpace_lof_lof {X Y Z : Cᵍʳ} {m n : ℤ}
    (g : ShiftedHom (Y : C) (Z : C) m) (f : ShiftedHom (X : C) (Y : C) n) :
    compSpace C
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (Y : C) (Z : C) i) m) g)
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n) f) =
      (DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (X : C) (Z : C) i) (n + m))
        (compHomDegree C g f) := sorry

/-- Zero is a left zero for composition on total shifted-Hom spaces. -/
@[simp] theorem compSpace_zero_left {X Y Z : Cᵍʳ} (f : homSpace C X Y) :
    compSpace C (0 : homSpace C Y Z) f = 0 := sorry

/-- Zero is a right zero for composition on total shifted-Hom spaces. -/
@[simp] theorem compSpace_zero_right {X Y Z : Cᵍʳ} (g : homSpace C Y Z) :
    compSpace C g (0 : homSpace C X Y) = 0 := sorry

/-- Composition on total shifted-Hom spaces is additive in its left input. -/
@[simp] theorem compSpace_add_left {X Y Z : Cᵍʳ}
    (g₁ g₂ : homSpace C Y Z) (f : homSpace C X Y) :
    compSpace C (g₁ + g₂) f = compSpace C g₁ f + compSpace C g₂ f := sorry

/-- Composition on total shifted-Hom spaces is additive in its right input. -/
@[simp] theorem compSpace_add_right {X Y Z : Cᵍʳ}
    (g : homSpace C Y Z) (f₁ f₂ : homSpace C X Y) :
    compSpace C g (f₁ + f₂) = compSpace C g f₁ + compSpace C g f₂ := sorry

/-- Composition on total shifted-Hom spaces commutes with integer scalars on the left. -/
@[simp] theorem compSpace_smul_left {X Y Z : Cᵍʳ}
    (r : ℤ) (g : homSpace C Y Z) (f : homSpace C X Y) :
    compSpace C (r • g) f = r • compSpace C g f := sorry

/-- Composition on total shifted-Hom spaces commutes with integer scalars on the right. -/
@[simp] theorem compSpace_smul_right {X Y Z : Cᵍʳ}
    (r : ℤ) (g : homSpace C Y Z) (f : homSpace C X Y) :
    compSpace C g (r • f) = r • compSpace C g f := sorry

/-- The category structure on `Cᵍʳ` induced by homogeneous shifted-Hom composition. -/
@[stacks 09P3 "category structure on shifted-Hom categories"]
instance instCategory : Category (Cᵍʳ) where
  Hom X Y := homSpace C X Y
  id := idSpace C
  comp f g := compSpace C g f
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The preadditive structure on `Cᵍʳ` induced by its direct-sum Hom groups. -/
@[stacks 09P3 "preadditive structure on shifted-Hom categories"]
instance instPreadditive : Preadditive (Cᵍʳ) where
  homGroup X Y := inferInstanceAs (AddCommGroup (homSpace C X Y))
  add_comp := sorry
  comp_add := sorry

end Composition

/-- The object `X[n]` of `Cᵍʳ`, obtained by shifting its underlying object in `C`. -/
abbrev shiftObj (X : Cᵍʳ) (n : ℤ) : Cᵍʳ :=
  of C ((X : C)⟦n⟧)

/-- Simultaneous shift of source and target on one homogeneous piece. -/
def shiftHomLinear [h_shift_additive : ∀ n : ℤ, (shiftFunctor C n).Additive]
    {X Y : Cᵍʳ} (n i : ℤ) :
    shiftedHom C X Y i →ₗ[ℤ] shiftedHom C (shiftObj C X n) (shiftObj C Y n) i where
  toFun f := (shiftFunctor C n).map f ≫ (shiftFunctorComm C i n).hom.app (Y : C)
  map_add' := sorry
  map_smul' := sorry

section Shift

variable [shift_additive : ∀ n : ℤ, (shiftFunctor C n).Additive]

/-- Simultaneous shift on the total shifted-Hom space. -/
def shiftMap {X Y : Cᵍʳ} (n : ℤ) :
    homSpace C X Y →ₗ[ℤ] homSpace C (shiftObj C X n) (shiftObj C Y n) :=
  DirectSum.toModule ℤ ℤ (homSpace C (shiftObj C X n) (shiftObj C Y n))
    (fun i ↦ (DirectSum.lof ℤ ℤ
      (fun j ↦ shiftedHom C (shiftObj C X n) (shiftObj C Y n) j) i).comp
        (shiftHomLinear C n i))

/-- `shiftMap` sends a homogeneous generator to the corresponding shifted generator. -/
@[simp] theorem shiftMap_lof {X Y : Cᵍʳ} (n i : ℤ)
    (f : ShiftedHom (X : C) (Y : C) i) :
    shiftMap C n ((DirectSum.lof ℤ ℤ (fun j ↦ shiftedHom C X Y j) i) f) =
      (DirectSum.lof ℤ ℤ
        (fun j ↦ shiftedHom C (shiftObj C X n) (shiftObj C Y n) j) i)
        ((shiftFunctor C n).map f ≫ (shiftFunctorComm C i n).hom.app (Y : C)) := sorry

/-- The inherited shift functor on `Cᵍʳ`. -/
def shift (n : ℤ) : Cᵍʳ ⥤ Cᵍʳ where
  obj X := shiftObj C X n
  map f := shiftMap C n f
  map_id := sorry
  map_comp := sorry

/-- The underlying object of `shift C n` applied to `X`. -/
@[simp] theorem shift_obj (n : ℤ) (X : Cᵍʳ) :
    ((shift C n).obj X : C) = (X : C)⟦n⟧ := sorry

end Shift

end Basic

section Linear

open scoped ShiftedHomCategory

variable (R : Type w) [Ring R]
variable [Preadditive C] [Linear R C] [HasShift C ℤ]

/-- The `R`-linear structure on `Cᵍʳ`, induced summandwise from shifted morphisms. -/
@[stacks 09P3 "linear structure on shifted-Hom categories"]
instance instLinear
    [h_shift_additive : ∀ n : ℤ, (shiftFunctor C n).Additive]
    [h_shift_linear : ∀ n : ℤ, Functor.Linear R (shiftFunctor C n)] :
    Linear R (Cᵍʳ) where
  homModule X Y := inferInstanceAs (Module R (homSpace C X Y))
  smul_comp := sorry
  comp_smul := sorry

section Grading

variable [shift_additive : ∀ n : ℤ, (shiftFunctor C n).Additive]
variable [shift_linear : ∀ n : ℤ, Functor.Linear R (shiftFunctor C n)]

/-- The degree-`n` submodule of the total Hom module in `Cᵍʳ`. -/
abbrev gradedHomDegree (X Y : Cᵍʳ) (n : ℤ) : Submodule R (X ⟶ Y) :=
  (DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n).range

/-- Include a shifted morphism as an element of its homogeneous submodule. -/
def gradedHomDegreeOf (X Y : Cᵍʳ) (n : ℤ) :
    ShiftedHom (X : C) (Y : C) n →ₗ[R] gradedHomDegree C R X Y n where
  toFun f := ⟨DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n f, ⟨f, rfl⟩⟩
  map_add' := sorry
  map_smul' := sorry

/-- The `n`-th shifted-Hom module is canonically the degree-`n` homogeneous submodule. -/
def gradedHomDegreeEquiv (X Y : Cᵍʳ) (n : ℤ) :
    ShiftedHom (X : C) (Y : C) n ≃ₗ[R] gradedHomDegree C R X Y n where
  toFun := gradedHomDegreeOf C R X Y n
  invFun x := DirectSum.component R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n x.1
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- Decompose the total shifted-Hom space into its homogeneous submodules. -/
def homSpaceDecompose (X Y : Cᵍʳ) :
    homSpace C X Y →ₗ[R] ⨁ n : ℤ, gradedHomDegree C R X Y n :=
  DirectSum.toModule R ℤ (⨁ n : ℤ, gradedHomDegree C R X Y n)
    (fun n ↦ (DirectSum.lof R ℤ (fun i ↦ gradedHomDegree C R X Y i) n).comp
      (gradedHomDegreeEquiv C R X Y n).toLinearMap)

/-- The canonical direct-sum decomposition of a total shifted-Hom space. -/
@[stacks 09P3 "direct-sum decomposition of shifted-Hom spaces"]
instance instHomSpaceDecomposition (X Y : Cᵍʳ) :
    DirectSum.Decomposition (gradedHomDegree C R X Y) :=
  DirectSum.Decomposition.ofLinearMap (gradedHomDegree C R X Y) (homSpaceDecompose C R X Y)
    (sorry) (sorry)

/-- The canonical grading on `Cᵍʳ` by shifted-Hom degree. -/
@[stacks 09P3, reducible]
def gradedCategory : GradedCategory R (Cᵍʳ) ℤ where
  homDegree := gradedHomDegree C R
  homDecomposition := instHomSpaceDecomposition C R
  id_mem_homDegree_zero := sorry
  comp_mem := sorry

variable (X Y : Cᵍʳ) (n : ℤ)

/-- The degree-`n` morphisms in `Cᵍʳ` are canonically `ShiftedHom (X : C) (Y : C) n`. -/
@[stacks 09P3]
def homDegreeEquivShiftedHom :
    gradedHomDegree C R X Y n ≃ₗ[R] ShiftedHom (X : C) (Y : C) n :=
  (gradedHomDegreeEquiv C R X Y n).symm

/-- The homogeneous-piece equivalence sends a canonical generator to its shifted morphism. -/
@[simp] theorem homDegreeEquivShiftedHom_apply_lof
    (f : ShiftedHom (X : C) (Y : C) n) :
    homDegreeEquivShiftedHom C R X Y n
      ⟨DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n f, ⟨f, rfl⟩⟩ = f := sorry

/-- The inverse homogeneous-piece equivalence is the canonical direct-sum generator. -/
@[simp] theorem homDegreeEquivShiftedHom_symm_apply
    (f : ShiftedHom (X : C) (Y : C) n) :
    (((homDegreeEquivShiftedHom C R X Y n).symm f :
        gradedHomDegree C R X Y n) : X ⟶ Y) =
      DirectSum.lof R ℤ (fun i ↦ ShiftedHom (X : C) (Y : C) i) n f := sorry

/-- The degree-zero morphisms in `Cᵍʳ` recover the ordinary morphisms in `C`. -/
abbrev degreeZeroHomEquiv (X Y : Cᵍʳ) :
    gradedHomDegree C R X Y 0 ≃ₗ[R] ((X : C) ⟶ Y) :=
  (homDegreeEquivShiftedHom C R X Y 0).trans
    (Linear.homCongr R (Iso.refl (X : C)) ((shiftFunctorZero' C (0 : ℤ) rfl).app (Y : C)))

/-- Shifting the target by `n` translates homogeneous degree `i` to degree `n + i`. -/
@[stacks 09P3]
abbrev homDegreeShiftObjEquiv (X Y : Cᵍʳ) (i n : ℤ) :
    gradedHomDegree C R X (shiftObj C Y n) i ≃ₗ[R]
      gradedHomDegree C R X Y (n + i) :=
  ((homDegreeEquivShiftedHom C R X (shiftObj C Y n) i).trans
    (Linear.homCongr R (Iso.refl (X : C)) (shiftAdd (Y : C) n i).symm)).trans
    (homDegreeEquivShiftedHom C R X Y (n + i)).symm

end Grading

end Linear

end ShiftedHomCategory

end

end CategoryTheory
