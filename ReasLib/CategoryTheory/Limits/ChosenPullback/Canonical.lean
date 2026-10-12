/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical and mapped chosen pullbacks

This module provides the neutral data-level API for passing between ordinary
chosen pullbacks and the `ChosenPullback` / `ChosenPullback₃` presentation used
by descent data.  It deliberately requires preservation only of the cospans
that occur in a construction.
-/

@[expose] public section

noncomputable section

universe uC uD vC vD

namespace CategoryTheory.Limits

namespace ChosenPullback

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {X Y U : C} (f : X ⟶ U) (g : Y ⟶ U)

/-- The canonical `ChosenPullback` associated to mathlib's selected pullback of `f` and `g`. -/
noncomputable def ofHasPullback [HasPullback f g] : ChosenPullback f g where
  pullback := CategoryTheory.Limits.pullback f g
  p₁ := CategoryTheory.Limits.pullback.fst f g
  p₂ := CategoryTheory.Limits.pullback.snd f g
  condition := CategoryTheory.Limits.pullback.condition
  isLimit := pullbackIsPullback f g

variable {f g}

/-- The canonical chosen pullback obtained from an ordinary proof argument.
This is the explicit-parameter companion to `ofHasPullback`; it lets callers
reuse a local pullback-existence theorem without installing a temporary
instance. -/
noncomputable def ofHasPullbackProof (h : HasPullback f g) :
    ChosenPullback f g :=
  @ofHasPullback C _ X Y U f g h

/-- Mapping the square equation of a chosen pullback along a functor gives the square equation
of its image. -/
theorem map_condition (u : C ⥤ D) (h : ChosenPullback f g) :
    u.map h.p₁ ≫ u.map f = u.map h.p₂ ≫ u.map g := sorry

/-- The explicit image cone of a chosen pullback is limiting when the functor preserves its
cospan. -/
noncomputable def map_isLimit (u : C ⥤ D) (h : ChosenPullback f g)
    [PreservesLimit (cospan f g) u] :
    IsLimit (PullbackCone.mk (u.map h.p₁) (u.map h.p₂) (map_condition u h)) :=
  isLimitPullbackConeMapOfIsLimit u _ h.isLimit

/-- The mapped first projection has the mapped common base map. -/
theorem map_hp₁ (u : C ⥤ D) (h : ChosenPullback f g) :
    u.map h.p₁ ≫ u.map f = u.map h.p := sorry

/-- A functor preserving the pullback cospan sends a chosen pullback to a chosen pullback of
the mapped arrows, retaining the explicit source object and projection maps. -/
noncomputable def map (u : C ⥤ D) (h : ChosenPullback f g)
    [PreservesLimit (cospan f g) u] :
    ChosenPullback (u.map f) (u.map g) where
  pullback := u.obj h.pullback
  p₁ := u.map h.p₁
  p₂ := u.map h.p₂
  condition := map_condition u h
  isLimit := map_isLimit u h
  p := u.map h.p
  hp₁ := map_hp₁ u h

end ChosenPullback

namespace ChosenPullback₃

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {X₁ X₂ X₃ U : C}
variable {f₁ : X₁ ⟶ U} {f₂ : X₂ ⟶ U} {f₃ : X₃ ⟶ U}

/-- The outer-pullback lift needed to assemble a threefold chosen pullback from the pullback of
the two middle projections. Its morphism is explicit; compatibility equations remain the proof
fields of mathlib's `ChosenPullback.LiftStruct`. -/
abbrev MiddleLift
    (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃)
    (h₁₃ : ChosenPullback f₁ f₃) (h : ChosenPullback h₁₂.p₂ h₂₃.p₁) :=
  h₁₃.LiftStruct (h.p₁ ≫ h₁₂.p₁) (h.p₂ ≫ h₂₃.p₂) (h.p₁ ≫ h₁₂.p)

namespace MiddleLift

/-- The outer lift needed for a threefold pullback exists. This proposition does not choose the
lift, so deferred proof work cannot enter the assembled morphism data. -/
theorem nonempty
    (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃)
    (h₁₃ : ChosenPullback f₁ f₃) (h : ChosenPullback h₁₂.p₂ h₂₃.p₁) :
    Nonempty (MiddleLift h₁₂ h₂₃ h₁₃ h) := sorry

end MiddleLift

/-- Assemble three pairwise chosen pullbacks into their threefold overlap by pulling back the
two middle projections. -/
def ofMiddle
    (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃)
    (h₁₃ : ChosenPullback f₁ f₃) (h : ChosenPullback h₁₂.p₂ h₂₃.p₁)
    (outerLift : MiddleLift h₁₂ h₂₃ h₁₃ h) :
    ChosenPullback₃ h₁₂ h₂₃ h₁₃ where
  chosenPullback := h
  l := outerLift

variable {h₁₂ : ChosenPullback f₁ f₂} {h₂₃ : ChosenPullback f₂ f₃}
variable {h₁₃ : ChosenPullback f₁ f₃}

/-- Mapping the outer-pullback lift of a threefold chosen pullback preserves its first
projection. -/
theorem map_lift_p₁ (u : C ⥤ D) (h : ChosenPullback₃ h₁₂ h₂₃ h₁₃)
    [PreservesLimit (cospan f₁ f₃) u] :
    u.map h.l.f ≫ (ChosenPullback.map u h₁₃).p₁ = u.map h.p₁ := sorry

/-- Mapping the outer-pullback lift of a threefold chosen pullback preserves its second
projection. -/
theorem map_lift_p₂ (u : C ⥤ D) (h : ChosenPullback₃ h₁₂ h₂₃ h₁₃)
    [PreservesLimit (cospan f₁ f₃) u] :
    u.map h.l.f ≫ (ChosenPullback.map u h₁₃).p₂ = u.map h.p₃ := sorry

/-- Mapping the outer-pullback lift of a threefold chosen pullback preserves its common base
map. -/
theorem map_lift_p (u : C ⥤ D) (h : ChosenPullback₃ h₁₂ h₂₃ h₁₃)
    [PreservesLimit (cospan f₁ f₃) u] :
    u.map h.l.f ≫ (ChosenPullback.map u h₁₃).p = u.map h.p := sorry

/-- The mapped first-wide projection is the first-wide projection of the mapped data. -/
theorem map_hp₁ (u : C ⥤ D) (h : ChosenPullback₃ h₁₂ h₂₃ h₁₃)
    [PreservesLimit (cospan f₁ f₂) u] [PreservesLimit (cospan h₁₂.p₂ h₂₃.p₁) u] :
    (ChosenPullback.map u h.chosenPullback).p₁ ≫ (ChosenPullback.map u h₁₂).p₁ =
      u.map h.p₁ := sorry

/-- The mapped third-wide projection is the third-wide projection of the mapped data. -/
theorem map_hp₃ (u : C ⥤ D) (h : ChosenPullback₃ h₁₂ h₂₃ h₁₃)
    [PreservesLimit (cospan f₂ f₃) u] [PreservesLimit (cospan h₁₂.p₂ h₂₃.p₁) u] :
    (ChosenPullback.map u h.chosenPullback).p₂ ≫ (ChosenPullback.map u h₂₃).p₂ =
      u.map h.p₃ := sorry

/-- A functor preserving the four pullback cospans underlying a threefold chosen pullback maps
the complete chosen threefold-overlap data. -/
noncomputable def map (u : C ⥤ D) (h : ChosenPullback₃ h₁₂ h₂₃ h₁₃)
    [PreservesLimit (cospan f₁ f₂) u] [PreservesLimit (cospan f₂ f₃) u]
    [PreservesLimit (cospan f₁ f₃) u] [PreservesLimit (cospan h₁₂.p₂ h₂₃.p₁) u] :
    ChosenPullback₃ (ChosenPullback.map u h₁₂) (ChosenPullback.map u h₂₃)
      (ChosenPullback.map u h₁₃) where
  chosenPullback := ChosenPullback.map u h.chosenPullback
  p := u.map h.p
  p₁ := u.map h.p₁
  p₃ := u.map h.p₃
  l :=
    { f := u.map h.l.f
      f_p₁ := map_lift_p₁ u h
      f_p₂ := map_lift_p₂ u h
      f_p := map_lift_p u h }
  hp₁ := map_hp₁ u h
  hp₃ := map_hp₃ u h

end ChosenPullback₃

end CategoryTheory.Limits
