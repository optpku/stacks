/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Localization.SemiRepresentable

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily

universe w v u

variable {C : Type u} [Category.{v} C]

#check (CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization.overMap_forget :
  ∀ {K L : FormalCoproduct.{w} C} (φ : K ⟶ L),
    overMap φ ⋙ SemiRepresentableFamily.forget L ≅ SemiRepresentableFamily.forget K)
