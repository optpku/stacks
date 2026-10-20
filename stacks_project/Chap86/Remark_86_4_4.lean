/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.BaseChange.Interchange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.TwoSquare

universe uA₁ uA₂ uA₃ uB₁ uB₂ uB₃ uC₁ uC₂ uC₃
  vA₁ vA₂ vA₃ vB₁ vB₂ vB₃ vC₁ vC₂ vC₃

variable {A₁ : Type uA₁} {A₂ : Type uA₂} {A₃ : Type uA₃}
  {B₁ : Type uB₁} {B₂ : Type uB₂} {B₃ : Type uB₃}
  {C₁ : Type uC₁} {C₂ : Type uC₂} {C₃ : Type uC₃}
variable [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vA₃} A₃]
  [Category.{vB₁} B₁] [Category.{vB₂} B₂] [Category.{vB₃} B₃]
  [Category.{vC₁} C₁] [Category.{vC₂} C₂] [Category.{vC₃} C₃]
variable {G₁ : A₁ ⥤ A₂} {G₂ : A₂ ⥤ A₃}
  {H₁ : B₁ ⥤ B₂} {H₂ : B₂ ⥤ B₃}
  {K₁ : C₁ ⥤ C₂} {K₂ : C₂ ⥤ C₃}
variable {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁}
  {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂}
  {L₃ : A₃ ⥤ B₃} {R₃ : B₃ ⥤ A₃}
  {L₄ : B₁ ⥤ C₁} {R₄ : C₁ ⥤ B₁}
  {L₅ : B₂ ⥤ C₂} {R₅ : C₂ ⥤ B₂}
  {L₆ : B₃ ⥤ C₃} {R₆ : C₃ ⥤ B₃}

/- Remark 86.4.4: In a `2 × 2` grid of cartesian squares of quasi-compact and
quasi-separated algebraic spaces over a scheme `S`, labeled `A B / C D`, with Tor-independent
pairs `(f, l)`, `(g, m)`, `(f', l')`, `(g', m')`, the four maps of 86.4.1.1 are inverse mates
`γ_A`, `γ_B`, `γ_C`, `γ_D`. Lemma 86.4.3 identifies `γ_{A+B} = γ_A ∘ γ_B` and
`γ_{C+D} = γ_C ∘ γ_D`; Lemma 86.4.2 identifies `γ_{A+C} = γ_C ∘ γ_A` and
`γ_{B+D} = γ_D ∘ γ_B`. The two composites around the grid then agree:
`γ_{A+C} ∘ γ_{B+D} = γ_{C+D} ∘ γ_{A+B}`. Once the maps are `mapOfRight`, this is
categorical interchange of horizontal and vertical paste. -/
@[stacks 0E5G] #check
  (CategoryTheory.DerivedBaseChange.mapOfRight_interchange :
    (adj₁ : L₁ ⊣ R₁) → (adj₂ : L₂ ⊣ R₂) → (adj₃ : L₃ ⊣ R₃) →
      (adj₄ : L₄ ⊣ R₄) → (adj₅ : L₅ ⊣ R₅) → (adj₆ : L₆ ⊣ R₆) →
        (s₁ : TwoSquare R₁ H₁ G₁ R₂) → (s₂ : TwoSquare R₂ H₂ G₂ R₃) →
          (s₃ : TwoSquare R₄ K₁ H₁ R₅) → (s₄ : TwoSquare R₅ K₂ H₂ R₆) →
            (CategoryTheory.DerivedBaseChange.mapOfRight adj₁ adj₂ s₁ ≫ₕ
                CategoryTheory.DerivedBaseChange.mapOfRight adj₂ adj₃ s₂) ≫ᵥ
                (CategoryTheory.DerivedBaseChange.mapOfRight adj₄ adj₅ s₃ ≫ₕ
                  CategoryTheory.DerivedBaseChange.mapOfRight adj₅ adj₆ s₄) =
              (CategoryTheory.DerivedBaseChange.mapOfRight adj₁ adj₂ s₁ ≫ᵥ
                  CategoryTheory.DerivedBaseChange.mapOfRight adj₄ adj₅ s₃) ≫ₕ
                (CategoryTheory.DerivedBaseChange.mapOfRight adj₂ adj₃ s₂ ≫ᵥ
                  CategoryTheory.DerivedBaseChange.mapOfRight adj₅ adj₆ s₄))
