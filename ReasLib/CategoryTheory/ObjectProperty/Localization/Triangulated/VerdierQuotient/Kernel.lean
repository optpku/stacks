/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Kernel
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization

@[expose] public section

/-!
# Kernels and Morphisms Inverted by Verdier Quotients

These statements convert objectwise vanishing conditions into the morphism
property required by `Localization.lift`.  They are kept separate from the
quotient construction so the latter remains a data-and-instance leaf.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.ObjectProperty

open Limits MorphismProperty Pretriangulated
open scoped ZeroObject

namespace VerdierQuotient

section Homological

variable {D : Type u₁} {A : Type u₂}
  [Category.{v₁} D] [Category.{v₂} A]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Abelian A]

/-- Stacks 05RJ: if a homological functor vanishes on `P`, it inverts the
cone-defined Verdier system `P.trW`. -/
@[stacks 05RJ]
theorem trW_isInvertedBy_of_le_homologicalKernel
    (P : ObjectProperty D) (H : D ⥤ A) [H.IsHomological]
    (hP : P ≤ H.homologicalKernel) :
    P.trW.IsInvertedBy H := by
  letI : H.ShiftSequence ℤ := Functor.ShiftSequence.tautological H ℤ
  intro X Y f hf
  have hf' := trW_monotone hP f hf
  exact (NatIso.isIso_map_iff (H.isoShiftZero ℤ) f).1
    ((H.mem_homologicalKernel_trW_iff f).1 hf' 0)

end Homological

section Triangulated

variable {D : Type u₁} {E : Type u₃}
  [Category.{v₁} D] [Category.{v₃} E]
  [HasZeroObject D] [HasZeroObject E]
  [HasShift D ℤ] [HasShift E ℤ]
  [Preadditive D] [Preadditive E]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated D] [Pretriangulated E]

/-- Stacks 05RJ: if an exact functor vanishes on `P`, it inverts the
cone-defined Verdier system `P.trW`. -/
@[stacks 05RJ]
theorem trW_isInvertedBy_of_le_kernel
    (P : ObjectProperty D) (F : D ⥤ E) [F.CommShift ℤ] [F.IsTriangulated]
    (hP : P ≤ F.kernel) :
    P.trW.IsInvertedBy F := by
  rintro X Y f ⟨Z, g, h, hT, hZ⟩
  exact (Triangle.isZero₃_iff_isIso₁ _
    (F.map_distinguished _ hT)).1 (hP Z hZ)

end Triangulated

section Kernel

variable {D : Type u₁} [Category.{v₁} D]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]
  (P : ObjectProperty D) [P.IsTriangulated]

/-- Stacks 05RK: the kernel of the Verdier quotient functor is the retract
closure of the object property being quotiented. -/
@[stacks 05RK]
theorem kernel_eq_retractClosure :
    Functor.kernel (verdierQuotientFunctor P) = P.retractClosure := by
  ext X
  constructor
  · intro hX
    have hmap : P.trW.Q.map (𝟙 X) = P.trW.Q.map (0 : X ⟶ X) := by
      rw [Functor.map_id, Functor.map_zero]
      exact hX.eq_zero_of_src _
    obtain ⟨Y, s, hs, hs₀⟩ :=
      (MorphismProperty.map_eq_iff_precomp P.trW.Q P.trW (𝟙 X) 0).1 hmap
    have hs_zero : s = 0 := by simpa using hs₀
    obtain ⟨Z, g, h, hT, hZ⟩ := hs
    obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ (Triangle.mk s g h) hT (𝟙 X)
      (by
        change s ≫ 𝟙 X = 0
        simpa using hs_zero)
    exact ⟨Z, hZ, ⟨{ i := g, r := r, retract := hr.symm }⟩⟩
  · rintro ⟨Y, hY, ⟨r⟩⟩
    have hW : P.trW (0 : (0 : D) ⟶ Y) :=
      trW.mk P (contractible_distinguished₁ Y) hY
    have : IsIso (P.trW.Q.map (0 : (0 : D) ⟶ Y)) :=
      Localization.inverts P.trW.Q P.trW _ hW
    have hY₀ : IsZero (P.trW.Q.obj Y) :=
      (P.trW.Q.map_isZero (isZero_zero D)).of_iso
        (asIso (P.trW.Q.map (0 : (0 : D) ⟶ Y))).symm
    change IsZero (P.trW.Q.obj X)
    rw [IsZero.iff_id_eq_zero]
    calc
      𝟙 (P.trW.Q.obj X) = P.trW.Q.map r.i ≫ P.trW.Q.map r.r :=
        (r.map P.trW.Q).retract.symm
      _ = 0 := by rw [hY₀.eq_zero_of_tgt (P.trW.Q.map r.i), zero_comp]

/-- Stacks 05RL: a retract-stable triangulated object property is recovered as the kernel of
its Verdier quotient functor. -/
@[stacks 05RL]
theorem kernel_eq_self [P.IsStableUnderRetracts] :
    Functor.kernel (verdierQuotientFunctor P) = P := by
  rw [kernel_eq_retractClosure, retractClosure_eq_self]

/-- An object belongs to the kernel of the Verdier quotient functor exactly
when it is a retract of an object satisfying `P`. -/
@[stacks 05RK]
theorem mem_kernel_iff (X : D) :
    Functor.kernel (verdierQuotientFunctor P) X ↔
      ∃ Y : D, P Y ∧ Nonempty (Retract X Y) := by
  rw [kernel_eq_retractClosure]
  simp only [prop_retractClosure_iff, exists_prop]

/-- Biproduct presentation of `mem_kernel_iff`. -/
@[stacks 05RK]
theorem mem_kernel_iff_biprod (X : D) :
    Functor.kernel (verdierQuotientFunctor P) X ↔
      ∃ (X' Y : D), P Y ∧ Nonempty (X ⊞ X' ≅ Y) := by
  rw [mem_kernel_iff]
  constructor
  · rintro ⟨Y, hY, ⟨r⟩⟩
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle r.i
    have hh : h = 0 := Triangle.mor₃_eq_zero_of_mono₁ _ hT (by
      change Mono r.i
      infer_instance)
    obtain ⟨e, _⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT hh
    exact ⟨Z, Y, hY, ⟨e.symm⟩⟩
  · rintro ⟨X', Y, hY, ⟨e⟩⟩
    exact ⟨Y, hY, ⟨{
      i := biprod.inl ≫ e.hom
      r := e.inv ≫ biprod.fst
      retract := by simp }⟩⟩

/-- The kernel of the Verdier quotient is initial among retract-stable object
properties containing `P`. -/
@[stacks 05RK]
theorem kernel_le_iff (R : ObjectProperty D) [R.IsStableUnderRetracts] :
    Functor.kernel (verdierQuotientFunctor P) ≤ R ↔ P ≤ R := by
  rw [kernel_eq_retractClosure, retractClosure_le_iff]

/-- The kernel of any localization model for `P.trW` is `P` when `P` is stable under retracts.
This formulation lets downstream developments use their chosen quotient category directly. -/
@[stacks 05RT "kernel of a chosen Verdier localization model"]
theorem kernel_eq_self_of_isLocalization
    {E : Type u₃} [Category.{v₃} E] [P.IsStableUnderRetracts]
    (L : D ⥤ E) [L.IsLocalization P.trW] :
    Functor.kernel L = P := by
  calc
    Functor.kernel L = Functor.kernel P.trW.Q := by
      ext X
      change IsZero (L.obj X) ↔ IsZero (P.trW.Q.obj X)
      let e := Localization.equivalenceFromModel L P.trW
      let α := Localization.qCompEquivalenceFromModelFunctorIso L P.trW
      constructor
      · intro hX
        exact IsZero.of_full_of_faithful_of_isZero e.functor _
          (hX.of_iso (α.app X))
      · intro hX
        have hX' : IsZero (e.functor.obj (P.trW.Q.obj X)) := by
          apply IsZero.of_full_of_faithful_of_isZero e.inverse _
          exact hX.of_iso (e.unitIso.app _).symm
        exact hX'.of_iso (α.app X).symm
    _ = P := kernel_eq_self P

/-- Objectwise form of `kernel_eq_self_of_isLocalization`. -/
@[stacks 05RT "kernel membership in a chosen Verdier localization model"]
theorem mem_kernel_iff_of_isLocalization
    {E : Type u₃} [Category.{v₃} E] [P.IsStableUnderRetracts]
    (L : D ⥤ E) [L.IsLocalization P.trW] (X : D) :
    Functor.kernel L X ↔ P X := by
  rw [kernel_eq_self_of_isLocalization P L]

end Kernel


end VerdierQuotient

end CategoryTheory.ObjectProperty
