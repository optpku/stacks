/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective objects detected by a separator

The subobjects of a separator form a canonical set-sized family of monomorphisms.  Lifting
against this family detects injective objects.  The construction belongs at the category level:
graded modules, sheaves of modules, and other Grothendieck categories use the same owner.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.InjectiveTest

variable {C : Type u} [Category.{v} C] [HasSeparator C]

/-- The canonical index type for injectivity tests: subobjects of a chosen separator. -/
abbrev index (C : Type u) [Category.{v} C] [HasSeparator C] :=
  Subobject (separator C)

/-- The source of the canonical test arrow indexed by a separator subobject. -/
abbrev source (t : index C) : C := t

/-- The common target of the canonical separator-subobject test arrows. -/
abbrev target (_t : index C) : C := separator C

/-- The canonical monomorphism from a separator subobject into the separator. -/
abbrev arrow (t : index C) : source t ⟶ target t := t.arrow

/-- Every canonical separator-subobject test arrow is a monomorphism. -/
instance arrow_mono (t : index C) : Mono (arrow t) :=
  Subobject.arrow_mono t

/-- An object is injective exactly when every map from a separator subobject extends to the
separator. -/
@[stacks 0FSN]
theorem injective_iff_lifts (I : C) :
    Injective I ↔
      ∀ t : index C, ∀ f : source t ⟶ I,
        ∃ g : target t ⟶ I, arrow t ≫ g = f := sorry

/-- The canonical separator-subobject data realizes the existential test-family formulation. -/
theorem exists_family :
    ∃ (T : Type u) (N N' : T → C) (ι : ∀ t, N t ⟶ N' t),
      (∀ t, Mono (ι t)) ∧
        ∀ I : C, Injective I ↔
          ∀ t (f : N t ⟶ I), ∃ g : N' t ⟶ I, ι t ≫ g = f := sorry

end CategoryTheory.InjectiveTest
