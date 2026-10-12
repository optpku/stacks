/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    x ⤳ y := sorry

/-- The endpoints of an immediate specialization are distinct. -/
theorem IsImmediateSpecialization.ne {x y : X} (h : IsImmediateSpecialization x y) :
    x ≠ y := sorry

/-- A point between the endpoints of an immediate specialization is one of the endpoints. -/
theorem IsImmediateSpecialization.eq_or_eq {x y z : X} (h : IsImmediateSpecialization x y)
    (hxz : x ⤳ z) (hzy : z ⤳ y) : z = x ∨ z = y := sorry

/-- In a `T₀` space, immediate specializations are precisely covers in the specialization order. -/
theorem isImmediateSpecialization_iff_covBy [T0Space X] {x y : X} :
    IsImmediateSpecialization x y ↔ toEquiv y ⋖ toEquiv x := sorry

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
        ∀ ⦃x y : X⦄, IsImmediateSpecialization x y → δ x = δ y + 1 := sorry

/-- A dimension function is weakly decreasing along specialization. -/
theorem IsDimensionFunction.le_of_specializes
    {δ : X → ℤ} (hδ : IsDimensionFunction δ) {x y : X} (hxy : x ⤳ y) :
    δ y ≤ δ x := sorry

/-- Along a specialization, equal dimension-function values characterize equal points. -/
theorem IsDimensionFunction.eq_iff_of_specializes
    {δ : X → ℤ} (hδ : IsDimensionFunction δ) {x y : X} (hxy : x ⤳ y) :
    δ x = δ y ↔ x = y := sorry

section Transport

variable {Y : Type v} [TopologicalSpace Y]

/-- Open embeddings preserve and reflect immediate specialization between source points. -/
theorem Topology.IsOpenEmbedding.isImmediateSpecialization_iff
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) {x y : X} :
    IsImmediateSpecialization (f x) (f y) ↔ IsImmediateSpecialization x y := sorry

/-- Pulling a dimension function back along an open embedding yields a dimension function. -/
theorem IsDimensionFunction.comp_isOpenEmbedding
    {δ : Y → ℤ} (hδ : IsDimensionFunction δ)
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) :
    IsDimensionFunction (δ ∘ f) := sorry

/-- Pullback along a homeomorphism preserves and reflects the dimension-function property. -/
theorem Homeomorph.isDimensionFunction_comp_iff (e : X ≃ₜ Y) (δ : Y → ℤ) :
    IsDimensionFunction (δ ∘ e) ↔ IsDimensionFunction δ := sorry

end Transport

/-- Locally constant functions take equal values at specialized points. -/
theorem IsLocallyConstant.eq_of_specializes
    {Y : Type v} {f : X → Y} (hf : IsLocallyConstant f) {x y : X} (hxy : x ⤳ y) :
    f x = f y := sorry

/-- Adding a locally constant integer-valued function preserves dimension functions. -/
theorem IsDimensionFunction.add_isLocallyConstant
    {δ ε : X → ℤ} (hδ : IsDimensionFunction δ) (hε : IsLocallyConstant ε) :
    IsDimensionFunction (δ + ε) := sorry

/-- Subtracting a locally constant integer-valued function preserves dimension functions. -/
theorem IsDimensionFunction.sub_isLocallyConstant
    {δ ε : X → ℤ} (hδ : IsDimensionFunction δ) (hε : IsLocallyConstant ε) :
    IsDimensionFunction (δ - ε) := sorry

/-- Translation by a locally constant function preserves and reflects the dimension-function
property. -/
theorem IsLocallyConstant.isDimensionFunction_add_iff
    {δ ε : X → ℤ} (hε : IsLocallyConstant ε) :
    IsDimensionFunction (δ + ε) ↔ IsDimensionFunction δ := sorry

/-- Subtraction of a locally constant function preserves and reflects the dimension-function
property. -/
theorem IsLocallyConstant.isDimensionFunction_sub_iff
    {δ ε : X → ℤ} (hε : IsLocallyConstant ε) :
    IsDimensionFunction (δ - ε) ↔ IsDimensionFunction δ := sorry

/-- Translating a dimension function by an integer constant preserves the dimension-function
property. -/
theorem IsDimensionFunction.sub_const
    {δ : X → ℤ} (hδ : IsDimensionFunction δ) (c : ℤ) :
    IsDimensionFunction (fun x ↦ δ x - c) := sorry

/-- A dimension function forces the ambient space to be `T₀`. -/
theorem IsDimensionFunction.t0Space {δ : X → ℤ} (hδ : IsDimensionFunction δ) :
    T0Space X := sorry

/-- The grading of the specialization order induced by a dimension function, with grade map
`δ ∘ ofEquiv`. -/
@[reducible]
protected noncomputable def IsDimensionFunction.gradeOrder {δ : X → ℤ}
    (hδ : IsDimensionFunction δ) : GradeOrder ℤ (Specialization X) where
  grade := δ ∘ ofEquiv
  grade_strictMono := sorry
  covBy_grade := sorry

/-- The grading supplied by a dimension function evaluates to the original function on the
underlying point. -/
@[simp]
theorem IsDimensionFunction.gradeOrder_apply {δ : X → ℤ}
    (hδ : IsDimensionFunction δ) (x : Specialization X) :
    hδ.gradeOrder.grade x = δ (ofEquiv x) := sorry

/-- The constant-zero function is a dimension function on a `T₁` space. -/
instance instIsDimensionFunctionZero [T1Space X] :
    IsDimensionFunction (fun _ : X ↦ (0 : ℤ)) where
  strict_of_specializes := sorry
  eq_add_one_of_immediateSpecialization := sorry
