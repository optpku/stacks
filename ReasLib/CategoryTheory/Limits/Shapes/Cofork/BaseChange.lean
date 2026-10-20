/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Base change of coforks

This module constructs the pullback of a cofork along a morphism to its point and records
the projection formulas for the resulting parallel arrows and cofork leg.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.Limits.Cofork

variable {C : Type u} [Category.{v} C]
variable {X Y : C} {f g : X ⟶ Y}

/-- The base change of the left parallel arrow of a cofork along a morphism to its point. -/
noncomputable def baseChangeLeft (t : Cofork f g) {T : C} (p : T ⟶ t.pt)
    [HasPullback (f ≫ t.π) p] [HasPullback t.π p] :
    pullback (f ≫ t.π) p ⟶ pullback t.π p :=
  pullback.map (f ≫ t.π) p t.π p f (𝟙 T) (𝟙 t.pt)
    (by simp) (by simp)

/-- The base change of the right parallel arrow of a cofork along a morphism to its point. -/
noncomputable def baseChangeRight (t : Cofork f g) {T : C} (p : T ⟶ t.pt)
    [HasPullback (f ≫ t.π) p] [HasPullback t.π p] :
    pullback (f ≫ t.π) p ⟶ pullback t.π p :=
  pullback.map (f ≫ t.π) p t.π p g (𝟙 T) (𝟙 t.pt)
    (by simpa using t.condition) (by simp)

/-- The left base-changed arrow has the expected first projection. -/
@[reassoc (attr := simp)]
theorem baseChangeLeft_fst (t : Cofork f g) {T : C} (p : T ⟶ t.pt)
    [HasPullback (f ≫ t.π) p] [HasPullback t.π p] :
    t.baseChangeLeft p ≫ pullback.fst t.π p =
      pullback.fst (f ≫ t.π) p ≫ f := sorry

/-- The left base-changed arrow has the expected second projection. -/
@[reassoc (attr := simp)]
theorem baseChangeLeft_snd (t : Cofork f g) {T : C} (p : T ⟶ t.pt)
    [HasPullback (f ≫ t.π) p] [HasPullback t.π p] :
    t.baseChangeLeft p ≫ pullback.snd t.π p =
      pullback.snd (f ≫ t.π) p := sorry

/-- The right base-changed arrow has the expected first projection. -/
@[reassoc (attr := simp)]
theorem baseChangeRight_fst (t : Cofork f g) {T : C} (p : T ⟶ t.pt)
    [HasPullback (f ≫ t.π) p] [HasPullback t.π p] :
    t.baseChangeRight p ≫ pullback.fst t.π p =
      pullback.fst (f ≫ t.π) p ≫ g := sorry

/-- The right base-changed arrow has the expected second projection. -/
@[reassoc (attr := simp)]
theorem baseChangeRight_snd (t : Cofork f g) {T : C} (p : T ⟶ t.pt)
    [HasPullback (f ≫ t.π) p] [HasPullback t.π p] :
    t.baseChangeRight p ≫ pullback.snd t.π p =
      pullback.snd (f ≫ t.π) p := sorry

/-- The cofork obtained by base changing a cofork along a morphism to its point. -/
noncomputable def baseChange (t : Cofork f g) {T : C} (p : T ⟶ t.pt)
    [HasPullback (f ≫ t.π) p] [HasPullback t.π p] :
  Cofork (t.baseChangeLeft p) (t.baseChangeRight p) :=
  Cofork.ofπ (pullback.snd t.π p)
    (by
      dsimp only [baseChangeLeft, baseChangeRight, pullback.map]
      rw [pullback.lift_snd, pullback.lift_snd])

/-- The leg of the base-changed cofork is the second pullback projection. -/
@[simp]
theorem baseChange_π (t : Cofork f g) {T : C} (p : T ⟶ t.pt)
    [HasPullback (f ≫ t.π) p] [HasPullback t.π p] :
    (t.baseChange p).π = pullback.snd t.π p := sorry

end CategoryTheory.Limits.Cofork
