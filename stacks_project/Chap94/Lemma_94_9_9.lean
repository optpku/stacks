/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 94.9.9: let `S` be a scheme contained in `Sch_fppf`. Let `X`, `Y`, `Z`
be categories fibred in groupoids over `(Sch/S)_fppf`. If `f : X ⟶ Y` and
`g : Y ⟶ Z` are 1-morphisms representable by algebraic spaces, then the
composite `f ≫ g : X ⟶ Z` is a 1-morphism representable by algebraic spaces. -/
@[stacks 0301]
#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.comp_mem :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Y ⟶ Z},
      relativelyRepresentableByAlgebraicSpaces f →
      relativelyRepresentableByAlgebraicSpaces g →
      relativelyRepresentableByAlgebraicSpaces (f ≫ g))
