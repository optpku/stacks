/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Grade
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Specialization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dimension functions on specialization orders

This module owns immediate specialization and integer-valued dimension functions on arbitrary
topological spaces, together with their transport and locally constant translation API.
-/

@[expose] public section

universe u v

open Specialization TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- `y` is an immediate specialization of `x` when it is a proper specialization and no point
lies strictly between the two endpoints. -/
@[stacks 02I9 "immediate specializations"]
def IsImmediateSpecialization (x y : X) : Prop :=
  x ⤳ y ∧ x ≠ y ∧ ∀ ⦃z : X⦄, x ⤳ z → z ⤳ y → z = x ∨ z = y

/-- An immediate specialization is a specialization. -/
theorem IsImmediateSpecialization.specializes {x y : X} (h : IsImmediateSpecialization x y) :
    x ⤳ y :=
  h.1

/-- The endpoints of an immediate specialization are distinct. -/
theorem IsImmediateSpecialization.ne {x y : X} (h : IsImmediateSpecialization x y) :
    x ≠ y :=
  h.2.1

/-- A point between the endpoints of an immediate specialization is one of the endpoints. -/
theorem IsImmediateSpecialization.eq_or_eq {x y z : X} (h : IsImmediateSpecialization x y)
    (hxz : x ⤳ z) (hzy : z ⤳ y) : z = x ∨ z = y :=
  h.2.2 hxz hzy

/-- In a `T₀` space, immediate specializations are precisely covers in the specialization order. -/
theorem isImmediateSpecialization_iff_covBy [T0Space X] {x y : X} :
    IsImmediateSpecialization x y ↔ toEquiv y ⋖ toEquiv x := by
  constructor
  · intro h
    refine covBy_of_eq_or_eq ?_ ?_
    · exact lt_of_le_of_ne h.specializes (by simpa [ne_comm] using h.ne)
    · intro z hyz hzx
      rcases h.eq_or_eq (z := ofEquiv z) hzx hyz with hz | hz
      · exact .inr (by simpa using congrArg toEquiv hz)
      · exact .inl (by simpa using congrArg toEquiv hz)
  · intro h
    refine ⟨h.le, ?_, ?_⟩
    · exact fun hxy ↦ h.ne (congrArg toEquiv hxy.symm)
    · intro z hxz hzy
      rcases h.eq_or_eq (c := toEquiv z) hzy hxz with hz | hz
      · exact .inr (toEquiv.injective hz)
      · exact .inl (toEquiv.injective hz)

/-- An integer-valued dimension function strictly decreases along proper specializations and
drops by one along immediate specializations. -/
@[stacks 02I9 "dimension functions"]
class IsDimensionFunction (δ : X → ℤ) : Prop where
  /-- Proper specializations strictly decrease the function. -/
  strict_of_specializes {x y : X} : x ⤳ y → x ≠ y → δ x > δ y
  /-- Immediate specializations decrease the function by exactly one. -/
  eq_add_one_of_immediateSpecialization {x y : X} :
    IsImmediateSpecialization x y → δ x = δ y + 1

/-- The two defining conditions for a dimension function. -/
theorem isDimensionFunction_iff {δ : X → ℤ} :
    IsDimensionFunction δ ↔
      (∀ ⦃x y : X⦄, x ⤳ y → x ≠ y → δ x > δ y) ∧
        ∀ ⦃x y : X⦄, IsImmediateSpecialization x y → δ x = δ y + 1 := by
  constructor
  · intro hδ
    exact ⟨fun {_ _} ↦ hδ.strict_of_specializes,
      fun {_ _} ↦ hδ.eq_add_one_of_immediateSpecialization⟩
  · rintro ⟨hstrict, himmediate⟩
    exact ⟨fun {_ _} hxy hne ↦ hstrict hxy hne, fun {_ _} hxy ↦ himmediate hxy⟩

/-- A dimension function is weakly decreasing along specialization. -/
theorem IsDimensionFunction.le_of_specializes
    {δ : X → ℤ} (hδ : IsDimensionFunction δ) {x y : X} (hxy : x ⤳ y) :
    δ y ≤ δ x := by
  by_cases h : x = y
  · subst y
    exact le_rfl
  · exact (hδ.strict_of_specializes hxy h).le

/-- Along a specialization, equal dimension-function values characterize equal points. -/
theorem IsDimensionFunction.eq_iff_of_specializes
    {δ : X → ℤ} (hδ : IsDimensionFunction δ) {x y : X} (hxy : x ⤳ y) :
    δ x = δ y ↔ x = y := by
  constructor
  · intro heq
    by_contra hne
    exact (ne_of_gt (hδ.strict_of_specializes hxy hne)) heq
  · rintro rfl
    rfl

section Transport

variable {Y : Type v} [TopologicalSpace Y]

/-- Open embeddings preserve and reflect immediate specialization between source points. -/
theorem Topology.IsOpenEmbedding.isImmediateSpecialization_iff
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) {x y : X} :
    IsImmediateSpecialization (f x) (f y) ↔ IsImmediateSpecialization x y := by
  constructor
  · intro h
    refine ⟨hf.isInducing.specializes_iff.mp h.specializes, ?_, ?_⟩
    · exact fun hxy ↦ h.ne (congrArg f hxy)
    · intro z hxz hzy
      rcases h.eq_or_eq (hxz.map hf.continuous) (hzy.map hf.continuous) with hz | hz
      · exact .inl (hf.injective hz)
      · exact .inr (hf.injective hz)
  · intro h
    refine ⟨h.specializes.map hf.continuous, ?_, ?_⟩
    · exact fun hxy ↦ h.ne (hf.injective hxy)
    · intro z hxz hzy
      obtain ⟨w, rfl⟩ := hzy.mem_open hf.isOpen_range ⟨y, rfl⟩
      rcases h.eq_or_eq (hf.isInducing.specializes_iff.mp hxz)
          (hf.isInducing.specializes_iff.mp hzy) with hw | hw
      · exact .inl (congrArg f hw)
      · exact .inr (congrArg f hw)

/-- Pulling a dimension function back along an open embedding yields a dimension function. -/
theorem IsDimensionFunction.comp_isOpenEmbedding
    {δ : Y → ℤ} (hδ : IsDimensionFunction δ)
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) :
    IsDimensionFunction (δ ∘ f) := by
  constructor
  · intro x y hxy hne
    exact hδ.strict_of_specializes (hxy.map hf.continuous)
      (fun heq ↦ hne (hf.injective heq))
  · intro x y hxy
    exact hδ.eq_add_one_of_immediateSpecialization
      (hf.isImmediateSpecialization_iff.mpr hxy)

/-- Pullback along a homeomorphism preserves and reflects the dimension-function property. -/
theorem Homeomorph.isDimensionFunction_comp_iff (e : X ≃ₜ Y) (δ : Y → ℤ) :
    IsDimensionFunction (δ ∘ e) ↔ IsDimensionFunction δ := by
  constructor
  · intro h
    simpa only [Function.comp_def, e.apply_symm_apply] using
      h.comp_isOpenEmbedding e.symm.isOpenEmbedding
  · exact fun h ↦ h.comp_isOpenEmbedding e.isOpenEmbedding

end Transport

/-- Locally constant functions take equal values at specialized points. -/
theorem IsLocallyConstant.eq_of_specializes
    {Y : Type v} {f : X → Y} (hf : IsLocallyConstant f) {x y : X} (hxy : x ⤳ y) :
    f x = f y := by
  exact hxy.mem_open (hf.isOpen_fiber (f y)) rfl

/-- Adding a locally constant integer-valued function preserves dimension functions. -/
theorem IsDimensionFunction.add_isLocallyConstant
    {δ ε : X → ℤ} (hδ : IsDimensionFunction δ) (hε : IsLocallyConstant ε) :
    IsDimensionFunction (δ + ε) := by
  constructor
  · intro x y hxy hne
    change δ y + ε y < δ x + ε x
    rw [hε.eq_of_specializes hxy]
    exact (add_lt_add_iff_right (ε y)).mpr (hδ.strict_of_specializes hxy hne)
  · intro x y hxy
    change δ x + ε x = (δ y + ε y) + 1
    rw [hδ.eq_add_one_of_immediateSpecialization hxy,
      hε.eq_of_specializes hxy.specializes]
    exact add_right_comm _ _ _

/-- Subtracting a locally constant integer-valued function preserves dimension functions. -/
theorem IsDimensionFunction.sub_isLocallyConstant
    {δ ε : X → ℤ} (hδ : IsDimensionFunction δ) (hε : IsLocallyConstant ε) :
    IsDimensionFunction (δ - ε) := by
  constructor
  · intro x y hxy hne
    change δ y - ε y < δ x - ε x
    rw [hε.eq_of_specializes hxy]
    exact sub_lt_sub_right (hδ.strict_of_specializes hxy hne) _
  · intro x y hxy
    change δ x - ε x = (δ y - ε y) + 1
    rw [hδ.eq_add_one_of_immediateSpecialization hxy,
      hε.eq_of_specializes hxy.specializes]
    exact add_sub_right_comm _ _ _

/-- Translation by a locally constant function preserves and reflects the dimension-function
property. -/
theorem IsLocallyConstant.isDimensionFunction_add_iff
    {δ ε : X → ℤ} (hε : IsLocallyConstant ε) :
    IsDimensionFunction (δ + ε) ↔ IsDimensionFunction δ := by
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using h.sub_isLocallyConstant hε
  · exact fun h ↦ h.add_isLocallyConstant hε

/-- Subtraction of a locally constant function preserves and reflects the dimension-function
property. -/
theorem IsLocallyConstant.isDimensionFunction_sub_iff
    {δ ε : X → ℤ} (hε : IsLocallyConstant ε) :
    IsDimensionFunction (δ - ε) ↔ IsDimensionFunction δ := by
  constructor
  · intro h
    simpa only [sub_add_cancel] using h.add_isLocallyConstant hε
  · exact fun h ↦ h.sub_isLocallyConstant hε

/-- Translating a dimension function by an integer constant preserves the dimension-function
property. -/
theorem IsDimensionFunction.sub_const
    {δ : X → ℤ} (hδ : IsDimensionFunction δ) (c : ℤ) :
    IsDimensionFunction (fun x ↦ δ x - c) :=
  hδ.sub_isLocallyConstant (IsLocallyConstant.const c)

/-- A dimension function forces the ambient space to be `T₀`. -/
theorem IsDimensionFunction.t0Space {δ : X → ℤ} (hδ : IsDimensionFunction δ) :
    T0Space X := by
  refine ⟨fun {x y} hxy ↦ ?_⟩
  apply (hδ.eq_iff_of_specializes hxy.specializes).mp
  exact le_antisymm (hδ.le_of_specializes hxy.specializes')
    (hδ.le_of_specializes hxy.specializes)

/-- The grading of the specialization order induced by a dimension function, with grade map
`δ ∘ ofEquiv`. -/
@[reducible]
protected noncomputable def IsDimensionFunction.gradeOrder {δ : X → ℤ}
    (hδ : IsDimensionFunction δ) : GradeOrder ℤ (Specialization X) where
  grade := δ ∘ ofEquiv
  grade_strictMono := by
    intro x y hxy
    exact hδ.strict_of_specializes (ofEquiv_specializes_ofEquiv.mpr hxy.le)
      (fun heq ↦ hxy.ne (ofEquiv.injective heq).symm)
  covBy_grade := by
    intro x y hxy
    letI : T0Space X := hδ.t0Space
    have himmediate : IsImmediateSpecialization (ofEquiv y) (ofEquiv x) :=
      isImmediateSpecialization_iff_covBy.mpr hxy
    exact Order.covBy_iff_add_one_eq.mpr
      (hδ.eq_add_one_of_immediateSpecialization himmediate).symm

/-- The grading supplied by a dimension function evaluates to the original function on the
underlying point. -/
@[simp]
theorem IsDimensionFunction.gradeOrder_apply {δ : X → ℤ}
    (hδ : IsDimensionFunction δ) (x : Specialization X) :
    hδ.gradeOrder.grade x = δ (ofEquiv x) :=
  rfl

/-- The constant-zero function is a dimension function on a `T₁` space. -/
instance instIsDimensionFunctionZero [T1Space X] :
    IsDimensionFunction (fun _ : X ↦ (0 : ℤ)) where
  strict_of_specializes := by
    intro x y hxy hne
    exact (hne (specializes_iff_eq.mp hxy)).elim
  eq_add_one_of_immediateSpecialization := by
    intro x y hxy
    exact (hxy.ne (specializes_iff_eq.mp hxy.specializes)).elim
