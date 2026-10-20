/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import Mathlib.CategoryTheory.MorphismProperty.Local
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
