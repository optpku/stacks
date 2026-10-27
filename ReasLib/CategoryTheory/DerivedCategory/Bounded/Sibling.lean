/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.EnoughNegativeObjects
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Triangulated.Functor

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA vA uA vD uD

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [_root_.CategoryTheory.IsTriangulated D]

/-- Two exact triangulated functors out of a bounded derived category are siblings when
their restrictions along the degree-zero heart inclusion are naturally isomorphic and
they take every bounded derived object to isomorphic objects. -/
def areSiblings
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated] : Prop :=
  Nonempty
      (DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F ≅
        DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F') ∧
    ∀ K : DerivedCategory.Bounded A, Nonempty (F.obj K ≅ F'.obj K)

/-- Sibling functors have naturally isomorphic restrictions to the degree-zero heart. -/
theorem areSiblings_restrict
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : areSiblings F F') :
    Nonempty
      (DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F ≅
        DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F') :=
  h.1

/-- Sibling functors take each bounded derived object to isomorphic objects. -/
theorem areSiblings_obj
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : areSiblings F F') (K : DerivedCategory.Bounded A) :
    Nonempty (F.obj K ≅ F'.obj K) :=
  h.2 K

/-- Essential surjectivity transfers between sibling exact triangulated functors. -/
theorem essSurj_of_areSiblings
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [_root_.CategoryTheory.IsTriangulated D]
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : areSiblings F F') [F.EssSurj] : F'.EssSurj where
  mem_essImage Y := by
    obtain ⟨K, ⟨e⟩⟩ := EssSurj.mem_essImage F Y
    obtain ⟨i⟩ := h.2 K
    exact ⟨K, ⟨i.symm ≪≫ e⟩⟩

/-- Full faithfulness transfers between sibling exact triangulated functors. -/
theorem fullyFaithful_of_areSiblings
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [_root_.CategoryTheory.IsTriangulated D]
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : areSiblings F F') (hF : Nonempty F.FullyFaithful) :
    Nonempty F'.FullyFaithful := sorry

/-- Every exact triangulated functor is sibling to itself. -/
theorem areSiblings_refl
    (F : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] : areSiblings F F :=
  ⟨⟨Iso.refl _⟩, fun K ↦ ⟨Iso.refl (F.obj K)⟩⟩

/-- Siblinghood is symmetric. -/
theorem areSiblings_symm
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : areSiblings F F') : areSiblings F' F := by
  refine ⟨?_, ?_⟩
  · show Nonempty
      (DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F' ≅
        DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F)
    obtain ⟨e⟩ := h.1
    exact ⟨e.symm⟩
  · show ∀ K, Nonempty (F'.obj K ≅ F.obj K)
    intro K
    obtain ⟨e⟩ := h.2 K
    exact ⟨e.symm⟩

/-- Siblinghood is transitive. -/
theorem areSiblings_trans
    (F F' F'' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [F'.CommShift ℤ] [F'.IsTriangulated]
    [F''.CommShift ℤ] [F''.IsTriangulated]
    (h₁ : areSiblings F F') (h₂ : areSiblings F' F'') :
    areSiblings F F'' := by
  refine ⟨?_, ?_⟩
  · show Nonempty
      (DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F ≅
        DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F'')
    obtain ⟨e₁⟩ := h₁.1
    obtain ⟨e₂⟩ := h₂.1
    exact ⟨e₁ ≪≫ e₂⟩
  · show ∀ K, Nonempty (F.obj K ≅ F''.obj K)
    intro K
    obtain ⟨e₁⟩ := h₁.2 K
    obtain ⟨e₂⟩ := h₂.2 K
    exact ⟨e₁ ≪≫ e₂⟩

/-- Exact triangulated functors with isomorphic restrictions to the heart and vanishing
negative shifted Homs between heart images are siblings. -/
theorem areSiblings_of_restrictIso_of_negShiftedHom
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [_root_.CategoryTheory.IsTriangulated D]
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (hiso : Nonempty (DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F ≅
        DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F'))
    (hvanish : ∀ (X Y : A) (q : ℤ), q < 0 →
      Subsingleton
        (ShiftedHom (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj X))
          (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj Y)) q)) :
    areSiblings F F' := sorry

/-- A fully faithful exact triangulated functor has subsingleton negative shifted Homs
between images of objects in the heart. -/
instance negShiftedHom_subsingleton_of_fullyFaithful
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [_root_.CategoryTheory.IsTriangulated D]
    (F : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful]
    (X Y : A) (q : ℤ) [Fact (q < 0)] :
    Subsingleton
      (ShiftedHom (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj X))
        (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj Y)) q) := by
  let I := DerivedCategory.Bounded.ι (C := A)
  let X₀ := (DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj X
  let Y₀ := (DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj Y
  have hzero (f : ShiftedHom X₀ Y₀ q) : f = 0 := by
    let e : I.obj (Y₀⟦q⟧) ≅ (I.obj Y₀)⟦q⟧ := (I.commShiftIso q).app Y₀
    apply I.map_injective
    rw [I.map_zero, ← cancel_mono e.hom, zero_comp]
    letI : (I.obj X₀).IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso
      ((DerivedCategory.Bounded.singleFunctorιIso A (0 : ℤ)).app X).symm 0
    letI : (I.obj Y₀).IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso
      ((DerivedCategory.Bounded.singleFunctorιIso A (0 : ℤ)).app Y).symm 0
    have := DerivedCategory.TStructure.t.isGE_shift
      (I.obj Y₀) 0 q (-q) (add_neg_cancel q)
    exact DerivedCategory.TStructure.t.zero _ 0 (-q) (neg_pos.mpr (Fact.out : q < 0))
  apply subsingleton_of_forall_eq (0 : ShiftedHom (F.obj X₀) (F.obj Y₀) q)
  intro f
  let e : F.obj (Y₀⟦q⟧) ≅ (F.obj Y₀)⟦q⟧ := (F.commShiftIso q).app Y₀
  obtain ⟨g, hg⟩ := F.map_surjective (f ≫ e.inv)
  rw [← cancel_mono e.inv, zero_comp, ← hg, hzero g, F.map_zero]

/-- Sibling exact triangulated functors from a bounded derived category are naturally
isomorphic if the abelian source has enough negative objects and the first functor
is fully faithful. -/
theorem isomorphic_of_areSiblings
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [_root_.CategoryTheory.IsTriangulated D]
    (hneg : HasEnoughNegativeObjects A)
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    [F.Full] [F.Faithful] (hsibling : areSiblings F F') :
    Nonempty (F ≅ F') := sorry

end CategoryTheory.Functor
