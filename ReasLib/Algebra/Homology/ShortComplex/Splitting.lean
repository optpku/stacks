/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic

/-! # Translation and difference of short-complex splittings -/

@[expose] public section

namespace CategoryTheory.ShortComplex.Splitting

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {S : ShortComplex C}

/-- Translating a section and its complementary retraction preserves the splitting identities. -/
theorem vadd_laws (s : S.Splitting) (φ : S.X₃ ⟶ S.X₁) :
    S.f ≫ (s.r - S.g ≫ φ) = 𝟙 _ ∧
      (s.s + φ ≫ S.f) ≫ S.g = 𝟙 _ ∧
        (s.r - S.g ≫ φ) ≫ S.f + S.g ≫ (s.s + φ ≫ S.f) = 𝟙 _ := sorry

/-- Translate a splitting by a morphism from its right endpoint to its left endpoint. -/
def vadd (s : S.Splitting) (φ : S.X₃ ⟶ S.X₁) : S.Splitting where
  r := s.r - S.g ≫ φ
  s := s.s + φ ≫ S.f
  f_r := (vadd_laws s φ).1
  s_g := (vadd_laws s φ).2.1
  id := (vadd_laws s φ).2.2

/-- The retraction of a translated splitting is the original retraction minus the endpoint composite. -/
theorem vadd_r (s : S.Splitting) (φ : S.X₃ ⟶ S.X₁) :
    (vadd s φ).r = s.r - S.g ≫ φ := rfl

/-- The section of a translated splitting is the original section plus the endpoint composite. -/
theorem vadd_s (s : S.Splitting) (φ : S.X₃ ⟶ S.X₁) :
    (vadd s φ).s = s.s + φ ≫ S.f := rfl

/-- The difference of two splitting sections is killed by the final map. -/
theorem vsub_zero (s₁ s₂ : S.Splitting) : (s₁.s - s₂.s) ≫ S.g = 0 := sorry

/-- Lift the difference of two splitting sections through the initial map of a short exact complex. -/
noncomputable def vsub (hS : S.ShortExact) (s₁ s₂ : S.Splitting) : S.X₃ ⟶ S.X₁ :=
  @ShortComplex.Exact.lift _ _ _ _ _ hS.exact _
    (s₁.s - s₂.s) (vsub_zero s₁ s₂) hS.mono_f

/-- Composing the splitting difference with the initial map recovers the difference of sections. -/
theorem vsub_f (hS : S.ShortExact) (s₁ s₂ : S.Splitting) :
    vsub hS s₁ s₂ ≫ S.f = s₁.s - s₂.s :=
  @ShortComplex.Exact.lift_f _ _ _ _ _ hS.exact _
    (s₁.s - s₂.s) (vsub_zero s₁ s₂) hS.mono_f

end CategoryTheory.ShortComplex.Splitting
