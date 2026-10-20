/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Monoidal.Universe
public import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Monoidal module sheaves in larger universes

This leaf exposes the monoidal structure on sheaves of modules induced by a
monoidal sheafification localization.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w m

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{max w m} Λ)]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat.{max w m} Λ))).IsMonoidal]

/-- The monoidal structure on sheaves of `Λ`-modules induced from the site-level monoidal
localization data. -/
instance moduleSheafMonoidalCategoryMax :
    MonoidalCategory (Sheaf J (ModuleCat.{max w m} Λ)) :=
  Sheaf.monoidalCategory J (ModuleCat.{max w m} Λ)

end CategoryTheory.Sheaf
