/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Over.FinitelyPresentable

/-!
# Finitely presented commutative algebras over a target

This leaf specializes the generic selected-over-object colimit API to
finitely presented commutative algebras over a fixed target algebra.

The stage carriers live in the universe of the target. The filtered-colimit
results assume `Small.{v} R` so that the base ring and finite polynomial algebras
can be used as stages in that universe. This is automatic for a base and target
in the same universe; the category and canonical cocone need no size assumption.

@stack 0BUF
@stack 07C3
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace CommAlgCat.Over.FinitePresentation

/-- The object property on `Over (CommAlgCat.of R A)` selecting the algebras
that are finitely presented over `R`. -/
@[stacks 0BUF "finitely presented algebras over a target"]
abbrev property (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] :
    ObjectProperty (CategoryTheory.Over (CommAlgCat.of R A)) :=
  fun B => Algebra.FinitePresentation R B.left

/-- The category of finitely presented `R`-algebras equipped with a map to
the target algebra `A`. -/
@[stacks 0BUF "finitely presented algebras over a target"]
abbrev category (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] :=
  (property R A).FullSubcategory

/-- The diagram of finitely presented `R`-algebras over `A`, after forgetting
their maps to `A`. -/
@[stacks 0BUF "finitely presented algebras over a target"]
abbrev diagram (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] :=
  CategoryTheory.ObjectProperty.Over.forgetDiagram (property R A)

/-- The canonical cocone from finitely presented `R`-algebras over `A` to
the target algebra `A`. -/
@[stacks 0BUF "finitely presented algebras over a target"]
abbrev cocone (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] :=
  CategoryTheory.ObjectProperty.Over.forgetCocone (property R A)

/-- Stacks `0BUF`: finitely presented `R`-algebras over `A` form a filtered
category and their canonical cocone has colimit `A`. -/
@[stacks 0BUF]
theorem isFilteredColimit (R : Type u) [CommRing R] [Small.{v} R]
    (A : Type v) [CommRing A] [Algebra R A] :
    IsFiltered (category R A) ∧ Nonempty (IsColimit (cocone R A)) := sorry

/-- Finitely presented `R`-algebras equipped with a map to `A` form a
filtered category. -/
@[stacks 0BUF "finitely presented algebras over a target form a filtered category"]
theorem isFiltered (R : Type u) [CommRing R] [Small.{v} R]
    (A : Type v) [CommRing A] [Algebra R A] :
    IsFiltered (category R A) :=
  (isFilteredColimit R A).1

/-- Typeclass form of `isFiltered` for the canonical category of finitely
presented algebras over a target. -/
@[stacks 0BUF "finitely presented algebras over a target form a filtered category"]
instance instIsFiltered (R : Type u) [CommRing R] [Small.{v} R]
    (A : Type v) [CommRing A] [Algebra R A] :
    IsFiltered (category R A) :=
  isFiltered R A

/-- The canonical cocone of finitely presented `R`-algebras over `A` admits a
colimit witness. -/
@[stacks 0BUF]
theorem cocone_hasColimit (R : Type u) [CommRing R] [Small.{v} R]
    (A : Type v) [CommRing A] [Algebra R A] :
    Nonempty (IsColimit (cocone R A)) :=
  (isFilteredColimit R A).2

/-- Stacks `07C3`: a family of finitely presented `R`-algebras over `A`
forms a filtered colimit presentation precisely when every finitely presented
`R`-algebra over `A` factors through one member of the family. -/
@[stacks 07C3]
theorem isFilteredColimit_iff_factorization
    {R : Type u} [CommRing R] [Small.{v} R]
    {A : Type v} [CommRing A] [Algebra R A]
    (P : ObjectProperty (CategoryTheory.Over (CommAlgCat.of R A)))
    (hfinitePresentation : ∀ B : CategoryTheory.Over (CommAlgCat.of R A),
      P B → Algebra.FinitePresentation R B.left) :
    (IsFiltered P.FullSubcategory ∧
      Nonempty (IsColimit (CategoryTheory.ObjectProperty.Over.forgetCocone P))) ↔
      ∀ (B : CategoryTheory.Over (CommAlgCat.of R A)),
        Algebra.FinitePresentation R B.left →
          ∃ D : P.FullSubcategory, Nonempty (B ⟶ D.obj) := sorry

end CommAlgCat.Over.FinitePresentation
