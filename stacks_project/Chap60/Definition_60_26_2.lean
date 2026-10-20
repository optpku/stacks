/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Frobenius.Crystal
import StacksCheckRecall

open CategoryTheory

universe u v

/- Definition 60.26.2: in Situation 60.26.1, take `C` to be the category of
crystals in finite locally free modules on `X/S` and `F` to be crystalline
Frobenius pullback relative to `σ`. An `F`-crystal is an object together with
a morphism from its Frobenius pullback to itself. -/
@[stacks 07N3] #check (CategoryTheory.FrobeniusCrystal :
  {C : Type u} → [Category.{v} C] → (C ⥤ C) → Type (max u v))

/- Nondegeneracy means that some `i : ℕ` and `V : 𝓔.obj ⟶ F.obj 𝓔.obj`
satisfy `𝓔.frobenius ≫ V = (p ^ i) • 𝟙 (F.obj 𝓔.obj)`. -/
#check (CategoryTheory.FrobeniusCrystal.IsNondegenerate :
  ∀ {C : Type u} [Category.{v} C] [Preadditive C] {F : C ⥤ C}
    (p : ℕ) [Fact (Nat.Prime p)], FrobeniusCrystal F → Prop)
