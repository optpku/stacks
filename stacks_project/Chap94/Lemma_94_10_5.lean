/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Composition of representable morphisms having a morphism property

A property `P` as in Definition 94.10.1 that is stable under composition is
inherited by composites of 1-morphisms of groupoid fibrations over
`(Sch/S)_fppf` that are representable by algebraic spaces and have `P`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 94.10.5: let `S` be a scheme in `Sch_fppf`. Let `X`, `Y`, `Z` be
categories fibred in groupoids over `(Sch/S)_fppf`. Let `P` be a property of
morphisms of algebraic spaces as in Definition 94.10.1 that is stable under
composition. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be 1-morphisms representable by
algebraic spaces. If `f` and `g` have `P`, then so does `f ≫ g` (Stacks `g ∘ f`).
Representability of the composite is Lemma 94.9.9, not this conclusion. -/
@[stacks 045B]
theorem has.comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [P.IsStableUnderComposition]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hg : relativelyRepresentableByAlgebraicSpaces g)
    (hfP : has P f) (hgP : has P g) : has P (f ≫ g) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
