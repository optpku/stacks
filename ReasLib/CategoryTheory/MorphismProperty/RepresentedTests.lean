/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Represented tests for morphism properties

A test family records all models, without selecting a representative.
The ambient category needs only a `CategoryStruct`, allowing bicategorical
1-morphisms. Ordinary categorical tests recover mathlib's `relative`.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

universe uC vC uD vD t m

section Core

variable (C : Type uC) [Category.{vC} C]
variable (D : Type uD) [CategoryStruct.{vD} D]

/-- Data specifying tests and all their possible represented pullback models.
`D` need only have a CategoryStruct, so a bicategory of 1-morphisms is allowed. -/
structure TestFamily where
  Test : ∀ {X Y : D}, (X ⟶ Y) → Type t
  Model : ∀ {X Y : D} (f : X ⟶ Y), Test f → Type m
  projection : ∀ {X Y : D} {f : X ⟶ Y} {a : Test f}, Model f a → Arrow C

variable {C D}

def TestFamily.representable (K : TestFamily.{uC, vC, uD, vD, t, m} C D) :
    MorphismProperty D :=
  fun _ _ f ↦ ∀ a : K.Test f, Nonempty (K.Model f a)

/-- This predicate alone can hold vacuously; relative includes representability. -/
def TestFamily.has (K : TestFamily.{uC, vC, uD, vD, t, m} C D)
    (P : MorphismProperty C) : MorphismProperty D :=
  fun _ _ f ↦ ∀ (a : K.Test f) (b : K.Model f a), P (K.projection b).hom

def TestFamily.relative (K : TestFamily.{uC, vC, uD, vD, t, m} C D)
    (P : MorphismProperty C) : MorphismProperty D :=
  K.representable ⊓ K.has P

theorem TestFamily.relative_mono (K : TestFamily.{uC, vC, uD, vD, t, m} C D)
    {P Q : MorphismProperty C} (h : P ≤ Q) : K.relative P ≤ K.relative Q := by
  intro X Y f hf
  exact ⟨hf.1, fun a b ↦ h _ (hf.2 a b)⟩

/-- Raw `has` and the representable property agree only with a supplied witness. -/
theorem TestFamily.relative_iff_has (K : TestFamily.{uC, vC, uD, vD, t, m} C D)
    (P : MorphismProperty C) {X Y : D} (f : X ⟶ Y)
    (hf : K.representable f) : K.relative P f ↔ K.has P f :=
  ⟨And.right, fun h ↦ ⟨hf, h⟩⟩

/-- A criterion for the same P is tested on the same represented projection.
This is the common interface to the RL-1825 criteria; no locality law is presumed. -/
theorem TestFamily.has_congr (K : TestFamily.{uC, vC, uD, vD, t, m} C D)
    {P Q : MorphismProperty C}
    (h : ∀ {A B : C} (g : A ⟶ B), P g ↔ Q g) {X Y : D} (f : X ⟶ Y) :
    K.has P f ↔ K.has Q f := by
  constructor
  · intro hP a b
    exact (h _).mp (hP a b)
  · intro hQ a b
    exact (h _).mpr (hQ a b)

namespace TestFamily.relative

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [CategoryStruct.{vD} D]
    {K : TestFamily.{uC, vC, uD, vD, t, m} C D} {P : MorphismProperty C}
    {X Y : D} {f : X ⟶ Y}

/-- A relative property includes existence of every represented test. -/
theorem rep (h : K.relative P f) : K.representable f := h.1

/-- Every actual represented projection has the underlying property. -/
theorem property (h : K.relative P f) (a : K.Test f) (b : K.Model f a) :
    P (K.projection b).hom := h.2 a b

/-- Assemble representability and the property on all models. -/
theorem of_models (hr : K.representable f) (hp : K.has P f) :
    K.relative P f := ⟨hr, hp⟩

end TestFamily.relative

end Core

section Ordinary

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Ordinary categorical specialization; no pullback or representation is chosen. -/
def ordinaryTests (F : C ⥤ D) : TestFamily C D where
  Test := fun {_ Y} _ ↦ Σ a : C, F.obj a ⟶ Y
  Model := fun {X _} f a ↦
    Σ b : C, Σ snd : b ⟶ a.1,
      { fst : F.obj b ⟶ X // IsPullback fst (F.map snd) f a.2 }
  projection := fun { _ _ _ _ } b ↦ Arrow.mk b.2.1

theorem ordinary_relative_iff (F : C ⥤ D) (P : MorphismProperty C)
    {X Y : D} (f : X ⟶ Y) :
    (ordinaryTests F).relative P f ↔ P.relative F f := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a g
      obtain ⟨b, s, l, hl⟩ := h.1 ⟨a, g⟩
      exact ⟨b, s, l, hl⟩
    · intro a b g l s hs
      exact h.2 ⟨a, g⟩ ⟨b, s, l, hs⟩
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨a, g⟩
      obtain ⟨b, s, l, hl⟩ := h.1 g
      exact ⟨b, s, l, hl⟩
    · rintro ⟨a, g⟩ ⟨b, s, l, hl⟩
      exact h.2 g l s hl

end Ordinary

end CategoryTheory.MorphismProperty
