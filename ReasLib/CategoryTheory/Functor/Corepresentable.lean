/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Elements
import Mathlib.Tactic.CrossRefAttribute

/-!
# Corepresentability criteria for type-valued functors

An initial object in the category of elements gives a corepresentation.  A small jointly
generating family of elements, together with limit preservation, supplies such an initial object.
-/

@[expose] public section

open CategoryTheory Limits

universe w v u uI

namespace CategoryTheory.Functor

/-- A type-valued functor is corepresentable if its category of elements has an initial object. -/
theorem isCorepresentable_of_hasInitial_elements
    {C : Type u} [Category.{v} C] {F : C ⥤ Type w}
    [HasInitial F.Elements] :
    F.IsCorepresentable := sorry

section

variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{v, v, v, u} C]
variable (F : C ⥤ Type w) [PreservesLimitsOfSize.{v, v} F]
variable {I : Type uI} [Small.{v} I]
variable (X : I → C) (x : ∀ i : I, F.obj (X i))

/-- A limit-preserving type-valued functor is corepresentable if a small family of elements
jointly generates every element under functorial images. -/
@[stacks 0AHN]
theorem isCorepresentable_of_preservesLimits_of_generating_family
    (h_generate :
      ∀ ⦃Y : C⦄ (g : F.obj Y),
        ∃ i : I, ∃ φ : X i ⟶ Y, F.map φ (x i) = g) :
    F.IsCorepresentable := sorry

end

end CategoryTheory.Functor
