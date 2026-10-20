/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.Countable.Opposite

/-!
# Countable Criteria for Idempotent Completeness

This leaf extends Mathlib's canonical owner `IsIdempotentComplete` with the
countable-product and countable-coproduct criteria used when kernels or
cokernels are available only for split morphisms.

The hypotheses are deliberately unbundled: they are useful both for concrete
categories and for subcategories whose split morphisms acquire (co)kernels by
a separate argument.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Idempotents

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The constant countable family on an object. -/
private abbrev powerFamily (X : C) : ℕ → C := fun _ ↦ X

section CountableProducts

variable [HasCountableProducts C]

/-- The countable power used in the idempotent swindle. -/
private noncomputable abbrev countablePower (X : C) : C :=
  ∏ᶜ powerFamily X

/-- A coordinate projection from the countable power. -/
private noncomputable abbrev proj (X : C) (n : ℕ) :
    countablePower X ⟶ X :=
  Pi.π (powerFamily X) n

/-- The left shift on a countable power. -/
private noncomputable def leftShift (X : C) :
    countablePower X ⟶ countablePower X :=
  Pi.lift fun n ↦ proj X (n + 1)

/-- The right shift on a countable power, with zero in the first coordinate. -/
private noncomputable def rightShift (X : C) :
    countablePower X ⟶ countablePower X :=
  Pi.lift fun
    | 0 => (0 : countablePower X ⟶ X)
    | n + 1 => proj X n

/-- The coordinatewise map between countable powers induced by a morphism. -/
private noncomputable def coordMap {X Y : C} (f : X ⟶ Y) :
    countablePower X ⟶ countablePower Y :=
  Limits.Pi.map (fun _ : ℕ ↦ f)

omit [Preadditive C] in
/-- A left shift followed by the `n`th projection is the successor projection. -/
private lemma leftShift_comp_proj (X : C) (n : ℕ) :
    leftShift X ≫ proj X n = proj X (n + 1) := by
  rw [leftShift, Pi.lift_π]

/-- The zeroth coordinate of the right shift vanishes. -/
private lemma rightShift_comp_proj_zero (X : C) :
    rightShift X ≫ proj X 0 = 0 := by
  rw [rightShift, Pi.lift_π]

/-- A right shift followed by a successor projection is the preceding projection. -/
private lemma rightShift_comp_proj_succ (X : C) (n : ℕ) :
    rightShift X ≫ proj X (n + 1) = proj X n := by
  rw [rightShift, Pi.lift_π]

omit [Preadditive C] in
/-- Coordinatewise maps commute with coordinate projections. -/
private lemma coordMap_comp_proj {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    coordMap f ≫ proj Y n = proj X n ≫ f := by
  simp [coordMap, proj]

/-- The Eilenberg-swindle map associated to an endomorphism. -/
private noncomputable def swindleMap {X : C} (p : X ⟶ X) :
    countablePower X ⟶ countablePower X :=
  coordMap p + leftShift X ≫ coordMap (𝟙 X - p)

/-- The candidate section of the swindle map associated to an endomorphism. -/
private noncomputable def swindleSection {X : C} (p : X ⟶ X) :
    countablePower X ⟶ countablePower X :=
  coordMap p + rightShift X ≫ coordMap (𝟙 X - p)

/-- The coordinate formula for the swindle map. -/
private lemma swindleMap_comp_proj {X : C} (p : X ⟶ X) (n : ℕ) :
    swindleMap p ≫ proj X n = proj X n ≫ p + proj X (n + 1) ≫ (𝟙 X - p) := by
  rw [swindleMap, Preadditive.add_comp]
  rw [coordMap_comp_proj]
  rw [Category.assoc, coordMap_comp_proj, ← Category.assoc, leftShift_comp_proj]

/-- The zeroth-coordinate formula for the candidate swindle section. -/
private lemma swindleSection_comp_proj_zero {X : C} (p : X ⟶ X) :
    swindleSection p ≫ proj X 0 = proj X 0 ≫ p := by
  rw [swindleSection, Preadditive.add_comp]
  rw [coordMap_comp_proj]
  rw [Category.assoc, coordMap_comp_proj, ← Category.assoc, rightShift_comp_proj_zero]
  simp

/-- The successor-coordinate formula for the candidate swindle section. -/
private lemma swindleSection_comp_proj_succ {X : C} (p : X ⟶ X) (n : ℕ) :
    swindleSection p ≫ proj X (n + 1) =
      proj X (n + 1) ≫ p + proj X n ≫ (𝟙 X - p) := by
  rw [swindleSection, Preadditive.add_comp]
  rw [coordMap_comp_proj]
  rw [Category.assoc, coordMap_comp_proj, ← Category.assoc, rightShift_comp_proj_succ]

/-- For an idempotent, the candidate swindle section is a section. -/
private lemma swindleSection_comp_swindleMap {X : C} (p : X ⟶ X) (hp : p ≫ p = p) :
    swindleSection p ≫ swindleMap p = 𝟙 (countablePower X) := by
  ext n
  cases n with
  | zero =>
      rw [Category.assoc, swindleMap_comp_proj, Preadditive.comp_add]
      rw [← Category.assoc, swindleSection_comp_proj_zero]
      rw [← Category.assoc, swindleSection_comp_proj_succ]
      simp [hp, Category.assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  | succ n =>
      rw [Category.assoc, swindleMap_comp_proj, Preadditive.comp_add]
      rw [← Category.assoc, swindleSection_comp_proj_succ]
      rw [← Category.assoc, swindleSection_comp_proj_succ]
      simp [hp, Category.assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- The map into a countable power supported in the zeroth coordinate. -/
private noncomputable def liftToPower {X W : C} (k : W ⟶ X) :
    W ⟶ countablePower X :=
  Pi.lift fun
    | 0 => k
    | _ + 1 => 0

/-- The zeroth projection of `liftToPower` recovers the original map. -/
private lemma liftToPower_comp_proj_zero {X W : C} (k : W ⟶ X) :
    liftToPower k ≫ proj X 0 = k := by
  rw [liftToPower, Pi.lift_π]

/-- Every successor projection of `liftToPower` vanishes. -/
private lemma liftToPower_comp_proj_succ {X W : C} (k : W ⟶ X) (n : ℕ) :
    liftToPower k ≫ proj X (n + 1) = 0 := by
  rw [liftToPower, Pi.lift_π]

/-- A map killed by `p` lifts to a map killed by the associated swindle map. -/
private lemma liftToPower_comp_swindleMap {X W : C} (p : X ⟶ X) (k : W ⟶ X)
    (hk : k ≫ p = 0) :
    liftToPower k ≫ swindleMap p = 0 := by
  ext n
  cases n with
  | zero =>
      rw [Category.assoc, swindleMap_comp_proj, Preadditive.comp_add]
      rw [← Category.assoc, liftToPower_comp_proj_zero]
      rw [← Category.assoc, liftToPower_comp_proj_succ]
      simp [hk]
  | succ n =>
      rw [Category.assoc, swindleMap_comp_proj, Preadditive.comp_add]
      rw [← Category.assoc, liftToPower_comp_proj_succ]
      rw [← Category.assoc, liftToPower_comp_proj_succ]
      simp

/-- The zeroth coordinate of a map killed by the swindle map is killed by the idempotent. -/
private lemma firstCoord_comp_p_eq_zero {X W : C} (p : X ⟶ X) (hp : p ≫ p = p)
    (u : W ⟶ countablePower X)
    (hu : u ≫ swindleMap p = 0) :
    (u ≫ proj X 0) ≫ p = 0 := by
  have h0 : u ≫ swindleMap p ≫ proj X 0 = 0 := by
    simpa [Category.assoc] using congrArg (fun g ↦ g ≫ proj X 0) hu
  have h0' : (u ≫ proj X 0) ≫ p + (u ≫ proj X 1) ≫ (𝟙 X - p) = 0 := by
    simpa [Category.assoc, swindleMap_comp_proj] using h0
  have hp' := congrArg (fun g ↦ g ≫ p) h0'
  simpa [hp, Category.assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp'

/-- Successor coordinates of a map killed by the swindle map are killed by `𝟙 X - p`. -/
private lemma succCoord_comp_one_sub_eq_zero {X W : C} (p : X ⟶ X) (hp : p ≫ p = p)
    (u : W ⟶ countablePower X)
    (hu : u ≫ swindleMap p = 0) (n : ℕ) :
    (u ≫ proj X (n + 1)) ≫ (𝟙 X - p) = 0 := by
  have hn : u ≫ swindleMap p ≫ proj X n = 0 := by
    simpa [Category.assoc] using congrArg (fun g ↦ g ≫ proj X n) hu
  have hn' : (u ≫ proj X n) ≫ p + (u ≫ proj X (n + 1)) ≫ (𝟙 X - p) = 0 := by
    simpa [Category.assoc, swindleMap_comp_proj] using hn
  have hq := congrArg (fun g ↦ g ≫ (𝟙 X - p)) hn'
  simpa [hp, Category.assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hq

/-- Successor coordinates of a map killed by the swindle map are killed by `p`. -/
private lemma succCoord_comp_p_eq_zero {X W : C} (p : X ⟶ X) (hp : p ≫ p = p)
    (u : W ⟶ countablePower X)
    (hu : u ≫ swindleMap p = 0) (n : ℕ) :
    (u ≫ proj X (n + 1)) ≫ p = 0 := by
  have hn : u ≫ swindleMap p ≫ proj X (n + 1) = 0 := by
    simpa [Category.assoc] using congrArg (fun g ↦ g ≫ proj X (n + 1)) hu
  have hn' : (u ≫ proj X (n + 1)) ≫ p + (u ≫ proj X (n + 2)) ≫ (𝟙 X - p) = 0 := by
    simpa [Category.assoc, swindleMap_comp_proj] using hn
  have hp' := congrArg (fun g ↦ g ≫ p) hn'
  simpa [hp, Category.assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp'

/-- Every successor coordinate of a map killed by the swindle map vanishes. -/
private lemma succCoord_eq_zero {X W : C} (p : X ⟶ X) (hp : p ≫ p = p)
    (u : W ⟶ countablePower X)
    (hu : u ≫ swindleMap p = 0) (n : ℕ) :
    u ≫ proj X (n + 1) = 0 := by
  have hp' := succCoord_comp_p_eq_zero p hp u hu n
  have hq := succCoord_comp_one_sub_eq_zero p hp u hu n
  calc
    u ≫ proj X (n + 1) =
        (u ≫ proj X (n + 1)) ≫ p + (u ≫ proj X (n + 1)) ≫ (𝟙 X - p) := by
      simp [Category.assoc, sub_eq_add_neg, add_left_comm, add_comm]
    _ = 0 := by simp [hp', hq]

/-- The countable-product swindle constructs a kernel for an idempotent from kernels of split
epimorphisms. -/
private theorem hasKernel_idempotent_of_splitEpiKernels
    (hkernel : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [IsSplitEpi f], HasKernel f)
    (X : C) (p : X ⟶ X) (hp : p ≫ p = p) : HasKernel p := by
  let f : countablePower X ⟶ countablePower X := swindleMap p
  let s : countablePower X ⟶ countablePower X := swindleSection p
  have hs : s ≫ f = 𝟙 (countablePower X) := by
    simpa [f, s] using swindleSection_comp_swindleMap p hp
  -- Local instance justification (proof-local temporary data): the explicit swindle section
  -- supplies the split-epimorphism hypothesis only for the proof-local map `f`.
  let : IsSplitEpi f := IsSplitEpi.mk' ⟨s, hs⟩
  -- Local instance justification (proof-local temporary data): the assumed kernel criterion is
  -- instantiated only at the proof-local swindle map so that the canonical kernel API applies.
  refine ⟨⟨KernelFork.ofι (kernel.ι f ≫ proj X 0) ?_, ?_⟩⟩
  · exact firstCoord_comp_p_eq_zero p hp (kernel.ι f) (kernel.condition f)
  · refine KernelFork.IsLimit.ofι (kernel.ι f ≫ proj X 0)
        (firstCoord_comp_p_eq_zero p hp (kernel.ι f) (kernel.condition f))
        (fun {W} k hk ↦ kernel.lift f (liftToPower k)
          (by simpa [f] using liftToPower_comp_swindleMap p k hk))
        (fun {W} k hk ↦ by
          rw [← Category.assoc, kernel.lift_ι, liftToPower_comp_proj_zero])
        (fun {W} k hk m hm ↦ by
          apply (cancel_mono (kernel.ι f)).1
          ext n
          cases n with
          | zero =>
              simpa [Category.assoc, liftToPower_comp_proj_zero] using hm
          | succ n =>
              have hm' : (m ≫ kernel.ι f) ≫ f = 0 := by
                rw [Category.assoc, kernel.condition, comp_zero]
              simpa [Category.assoc, liftToPower_comp_proj_succ] using
                succCoord_eq_zero p hp (m ≫ kernel.ι f) hm' n)

end CountableProducts

/-- A preadditive category with countable products is idempotent complete when every split
epimorphism has a kernel. -/
@[stacks 05QV]
theorem isIdempotentComplete_of_countableProducts_of_splitEpiKernels
    [HasCountableProducts C]
    (hkernel : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [IsSplitEpi f], HasKernel f) :
    IsIdempotentComplete C := by
  rw [isIdempotentComplete_iff_idempotents_have_kernels]
  intro X p hp
  exact hasKernel_idempotent_of_splitEpiKernels hkernel X p hp

/-- A preadditive category with countable coproducts is idempotent complete when every split
monomorphism has a cokernel. -/
@[stacks 05QV]
theorem isIdempotentComplete_of_countableCoproducts_of_splitMonoCokernels
    [HasCountableCoproducts C]
    (hcokernel : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [IsSplitMono f], HasCokernel f) :
    IsIdempotentComplete C := by
  have hkernelOp : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) [IsSplitEpi f], HasKernel f := by
    intro X Y f _
    -- Local instance justification (proof-local temporary data): the chosen section of the
    -- opposite split epimorphism gives the split-monomorphism witness needed only for `f.unop`.
    letI : IsSplitMono f.unop := IsSplitMono.mk' {
      retraction := (section_ f).unop
      id := by
        change (section_ f ≫ f).unop = (𝟙 Y).unop
        exact congrArg Quiver.Hom.unop (IsSplitEpi.id f) }
    -- Local instance justification (proof-local temporary data): the assumed cokernel criterion
    -- is instantiated only at `f.unop` to construct the corresponding opposite kernel.
    refine ⟨⟨KernelFork.ofι (cokernel.π f.unop).op ?_, ?_⟩⟩
    · have h := congrArg Quiver.Hom.op (cokernel.condition f.unop)
      change (cokernel.π f.unop).op ≫ f = 0 at h
      simpa using h
    · exact CokernelCofork.IsColimit.ofπOp (cokernel.π f.unop) (cokernel.condition f.unop)
        (cokernelIsCokernel f.unop)
  exact isIdempotentComplete_of_isIdempotentComplete_opposite <|
    isIdempotentComplete_of_countableProducts_of_splitEpiKernels hkernelOp

end CategoryTheory.Idempotents
