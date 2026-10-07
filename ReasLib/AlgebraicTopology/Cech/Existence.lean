module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Arrow.Opposite
public import ReasLib.CategoryTheory.Limits.WidePullback.Finite

/-!
# Existence conditions for Cech nerves and conerves

This file names the arrow-specific families of wide limits and colimits required by mathlib's
Cech constructions. The conditions are reducible propositions: they do not choose new limit
data and unfold directly to the instances expected by `Arrow.cechNerve` and
`Arrow.cechConerve`.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]

/-- The wide pullbacks required to form every degree of the Cech nerve of `f`. -/
@[stacks 016E "Cech-nerve existence condition"]
abbrev HasCechNerve (f : Arrow C) : Prop :=
  ∀ n : ℕ, HasWidePullback.{0} f.right
    (fun _ : Fin (n + 1) ↦ f.left) (fun _ ↦ f.hom)

/-- The wide pushouts required to form every degree of the Cech conerve of `f`. -/
@[stacks 016N "Cech-conerve existence condition"]
abbrev HasCechConerve (f : Arrow C) : Prop :=
  ∀ n : ℕ, HasWidePushout.{0} f.left
    (fun _ : Fin (n + 1) ↦ f.right) (fun _ ↦ f.hom)

namespace HasCechNerve

variable {X Y : C}

/-- Pullbacks construct every finite wide pullback occurring in the Cech nerve of an arrow. -/
@[stacks 018I "Cech-nerve existence from pullbacks"]
instance ofPullbacks (f : Arrow C) [HasPullbacks C] : f.HasCechNerve :=
  fun n ↦
    (HasPullbacks.widePullbackShape (C := C) (J := Fin (n + 1))).has_limit
      (WidePullbackShape.wideCospan f.right
        (fun _ : Fin (n + 1) ↦ f.left) (fun _ ↦ f.hom))

/-- Opposing an arrow with a Cech nerve supplies the wide pushout required in each degree of
the Cech conerve of the opposite arrow. -/
@[stacks 019Z "opposite Cech-nerve existence bridge"]
instance op (f : X ⟶ Y) [h : (Arrow.mk f).HasCechNerve] (n : ℕ) :
    HasWidePushout.{0} (Arrow.mk f.op).left
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).right)
      (fun _ ↦ (Arrow.mk f.op).hom) :=
  HasWidePullback.op (h n)

/-- A Cech nerve on an opposite-category arrow supplies a Cech conerve after applying the
inverse opposite-arrow functor. -/
@[stacks 019Z "inverse opposite-arrow Cech-nerve existence bridge"]
instance unopFunctor (f : Arrow Cᵒᵖ) [h : f.HasCechNerve] :
    ((Arrow.unopFunctor C).obj f).unop.HasCechConerve :=
  fun n ↦ HasWidePullback.unop (h n)

/-- The opposite-arrow functor exchanges Cech-nerve availability with Cech-conerve
availability. This named equivalence is the non-instance API for rewriting in either direction. -/
@[stacks 019Z "opposite-arrow Cech-nerve availability equivalence"]
theorem opFunctor_iff (f : Arrow C) :
    ((Arrow.opFunctor C).obj (Opposite.op f)).HasCechConerve ↔ f.HasCechNerve := sorry

/-- The inverse opposite-arrow functor exchanges Cech-nerve availability with Cech-conerve
availability. This is the bundled inverse form of `opFunctor_iff`. -/
@[stacks 019Z "inverse opposite-arrow Cech-nerve availability equivalence"]
theorem unopFunctor_iff (f : Arrow Cᵒᵖ) :
    ((Arrow.unopFunctor C).obj f).unop.HasCechConerve ↔ f.HasCechNerve := sorry

end HasCechNerve

namespace HasCechConerve

variable {X Y : C}

/-- Pushouts construct every finite wide pushout occurring in the Cech conerve of an arrow. -/
@[stacks 016N "Cech-conerve existence from pushouts"]
instance ofPushouts (f : Arrow C) [HasPushouts C] : f.HasCechConerve :=
  fun n ↦
    (HasPushouts.widePushoutShape (C := C) (J := Fin (n + 1))).has_colimit
      (WidePushoutShape.wideSpan f.left
        (fun _ : Fin (n + 1) ↦ f.right) (fun _ ↦ f.hom))

/-- Opposing an arrow with a Cech conerve supplies the wide pullback required in each degree of
the Cech nerve of the opposite arrow. -/
@[stacks 019Z "opposite Cech-conerve existence bridge"]
instance op (f : X ⟶ Y) [h : (Arrow.mk f).HasCechConerve] (n : ℕ) :
    HasWidePullback.{0} (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left)
      (fun _ ↦ (Arrow.mk f.op).hom) :=
  HasWidePushout.op (h n)

/-- A Cech conerve on an arrow supplies a Cech nerve after applying the opposite-arrow
functor. -/
@[stacks 019Z "opposite-arrow Cech-conerve existence bridge"]
instance opFunctor (f : (Arrow C)ᵒᵖ) [h : f.unop.HasCechConerve] :
    ((Arrow.opFunctor C).obj f).HasCechNerve :=
  fun n ↦ HasWidePushout.op (h n)

/-- The opposite-arrow functor exchanges Cech-conerve availability with Cech-nerve
availability. This named equivalence is the non-instance API for rewriting in either direction. -/
@[stacks 019Z "opposite-arrow Cech-conerve availability equivalence"]
theorem opFunctor_iff (f : Arrow C) :
    ((Arrow.opFunctor C).obj (Opposite.op f)).HasCechNerve ↔ f.HasCechConerve := sorry

/-- The inverse opposite-arrow functor exchanges Cech-conerve availability with Cech-nerve
availability. This is the bundled inverse form of `opFunctor_iff`. -/
@[stacks 019Z "inverse opposite-arrow Cech-conerve availability equivalence"]
theorem unopFunctor_iff (f : Arrow Cᵒᵖ) :
    ((Arrow.unopFunctor C).obj f).unop.HasCechNerve ↔ f.HasCechConerve := sorry

end HasCechConerve

end CategoryTheory.Arrow
