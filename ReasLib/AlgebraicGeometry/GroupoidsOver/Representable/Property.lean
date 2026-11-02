/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.CategoryTheory.MorphismProperty.RepresentedTests
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf

/-!
# Representable morphisms of groupoid fibrations having a morphism property

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` has a
property `P` of morphisms of algebraic spaces when every scheme-slice
representing morphism has `P`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A slice base-change model includes its actual projection and the full
existing representation predicate, including the projection triangle. -/
structure RepresentedModel {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) where
  space : AlgebraicSpace S
  hom : space ⟶ AlgebraicSpace.ofOver U
  represents : RepresentsBaseChange f y space hom

/-- All scheme-slice tests and all algebraic-space representations of them.
No representing space or equivalence is selected. -/
def spaceTests (S : Scheme.{u}) :
    MorphismProperty.TestFamily (AlgebraicSpace S) (GroupoidsOver S) where
  Test := fun {_ Y} _ ↦ Σ U : Over S, GroupoidsOver.slice U ⟶ Y
  Model := fun f a ↦ RepresentedModel f a.2
  projection := fun b ↦ Arrow.mk b.hom

/-- The generic existence predicate is precisely the existing representability. -/
theorem spaceTests_representable_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    (spaceTests S).representable f ↔ relativelyRepresentableByAlgebraicSpaces f := by
  constructor
  · intro h U y
    obtain ⟨b⟩ := h ⟨U, y⟩
    exact ⟨b.space, b.hom, b.represents⟩
  · rintro h ⟨U, y⟩
    obtain ⟨F, p, hp⟩ := h y
    exact ⟨⟨F, p, hp⟩⟩

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `Over S`
has a morphism property `P` of algebraic spaces when every scheme-slice
representing morphism `fy : Fy ⟶ AlgebraicSpace.ofOver U` satisfies `P`. -/
def has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) : Prop :=
  ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
    (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → P fy

/-- A 1-morphism has `P` if and only if every scheme-slice representing morphism
of algebraic spaces has `P`. -/
theorem has_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) :
    has P f ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy → P fy :=
  sorry

/-- A view of the original `has`, with the same vacuous behavior when a test
has no model. No base-change or locality assumptions are needed. -/
theorem has_iff_spaceTests {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) :
    has P f ↔ (spaceTests S).has P f := by
  constructor
  · rintro h ⟨U, y⟩ b
    exact h y b.space b.hom b.represents
  · intro h U y F p hp
    exact h ⟨U, y⟩ ⟨F, p, hp⟩

/-- The relative core adds precisely representability to the old property. -/
theorem spaceTests_relative_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) :
    (spaceTests S).relative P f ↔
      relativelyRepresentableByAlgebraicSpaces f ∧ has P f := by
  exact and_congr (spaceTests_representable_iff f) (has_iff_spaceTests P f).symm

namespace has

/-- A scheme-slice representing morphism of algebraic spaces for a 1-morphism
that has `P` itself has `P`. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y} (hf : has P f)
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    P fy :=
  sorry

/-- A 1-morphism has `P` if every scheme-slice representing morphism of algebraic
spaces has `P`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y}
    (h : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
      (fy : Fy ⟶ AlgebraicSpace.ofOver U),
      RepresentsBaseChange f y Fy fy → P fy) : has P f :=
  sorry

end has

/-- Having a morphism property stable under base change and fppf local on the
target is invariant under a 2-commutative square of groupoid fibrations whose
horizontal arrows are equivalences, provided the vertical morphisms are
representable by algebraic spaces. -/
theorem has.iff_of_equivalence {S : Scheme.{u}} {X' X Y' Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (eX : X' ≌ X) (eY : Y' ≌ Y) (f : X ⟶ Y) (f' : X' ⟶ Y')
    (sq : eX.hom ≫ f ≅ f' ≫ eY.hom)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has P f ↔ has P f' := sorry

/-- A 1-morphism representable by algebraic spaces that has a morphism property
`P` also has `P'` whenever `P` implies `P'` on morphisms of algebraic spaces,
provided both properties are stable under base change and fppf local on the
target. -/
theorem has.of_le {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {P P' : MorphismProperty (AlgebraicSpace S)}
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [P'.IsStableUnderBaseChange]
    [P'.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : P ≤ P') (hfP : has P f) : has P' f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
