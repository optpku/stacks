/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C]
variable (X : C)
variable [EnoughProjectives C]

/-!
# Definition 12.28.4

Compatibility facade for mathlib's canonical enough-projectives interface.
-/

/- Definition 12.28.4 [013E]: every object admits an epimorphism from a projective object. -/
@[stacks 013E]
#check (CategoryTheory.EnoughProjectives C : Prop)

#check (fun X : C => CategoryTheory.EnoughProjectives.presentation X :
  ∀ X : C, Nonempty (CategoryTheory.ProjectivePresentation X))
#check (CategoryTheory.ProjectivePresentation X : Type (max u v))
#check (CategoryTheory.Projective.over X : C)
#check (CategoryTheory.Projective.π X : CategoryTheory.Projective.over X ⟶ X)
