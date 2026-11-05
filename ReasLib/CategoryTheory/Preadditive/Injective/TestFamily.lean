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

The subobjects of a separator form a canonical family of monomorphisms. In a Grothendieck
abelian category, lifting against this family detects injective objects. The construction belongs
at the category level:
graded modules, sheaves of modules, and other Grothendieck categories use the same owner.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v w

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

/-- In a Grothendieck abelian category, an object is injective exactly when every map from a
separator subobject extends to the separator. -/
@[stacks 0FSN]
theorem injective_iff_lifts [Abelian C] [IsGrothendieckAbelian.{w} C] (I : C) :
    Injective I ↔
      ∀ t : index C, ∀ f : source t ⟶ I,
        ∃ g : target t ⟶ I, arrow t ≫ g = f := by
  constructor
  · intro hI t f
    exact @Injective.factors C _ I hI _ _ f (arrow t) inferInstance
  · intro h
    apply (injective_iff_rlp_monomorphisms_zero I).2
    rw [← IsGrothendieckAbelian.generatingMonomorphisms_rlp (isSeparator_separator C)]
    rintro _ _ _ ⟨t⟩
    constructor
    intro f g sq
    obtain ⟨l, hl⟩ := h t f
    exact ⟨⟨{ l := l, fac_left := hl, fac_right := (isZero_zero C).eq_of_tgt _ _ }⟩⟩

omit [HasSeparator C] in
/-- A (noncanonical) test family indexed by the noninjective objects. Classically choose one
failed monomorphism extension for each such object. This construction works in any category;
it does not identify this family with the separator-subobject family. -/
theorem exists_family [HasSeparator C] :
    ∃ (T : Type u) (N N' : T → C) (ι : ∀ t, N t ⟶ N' t),
      (∀ t, Mono (ι t)) ∧
        ∀ I : C, Injective I ↔
          ∀ t (f : N t ⟶ I), ∃ g : N' t ⟶ I, ι t ≫ g = f := by
  classical
  have hfailed : ∀ I : { I : C // ¬ Injective I },
      ∃ (A B : C) (i : A ⟶ B) (f : A ⟶ I.val),
        Mono i ∧ ¬ ∃ g : B ⟶ I.val, i ≫ g = f := by
    intro I
    by_contra h
    apply I.property
    constructor
    intro A B f i hi
    by_contra hf
    exact h ⟨A, B, i, f, hi, hf⟩
  choose A B i f hi hf using hfailed
  refine ⟨{ I : C // ¬ Injective I }, A, B, i, hi, ?_⟩
  intro I
  constructor
  · intro hI t f
    exact @Injective.factors C _ I hI _ _ f (i t) (hi t)
  · intro h
    by_contra hI
    exact hf ⟨I, hI⟩ (h ⟨I, hI⟩ (f ⟨I, hI⟩))

end CategoryTheory.InjectiveTest
