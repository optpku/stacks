/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Bounded
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Complex views of bounded-below finite filtered complexes

This leaf exposes the graded-piece and underlying cochain and homotopy complexes, together with
their maps.  It has no derived-category or left-exact-functor hypotheses.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The bounded-below complex underlying the `p`-th graded piece of a finite filtered complex. -/
@[stacks 015W "graded piece of a bounded-below finite filtered complex"]
noncomputable abbrev gradedPieceComplex
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) (p : ℤ) :
    CochainComplex.Plus A :=
  (FilteredObject.Finite.Plus.GradedPiece.cochain A p).obj K

/-- The bounded-below complex obtained by forgetting a finite filtration. -/
@[stacks 015W "underlying bounded-below complex of a finite filtered complex"]
noncomputable abbrev underlyingComplex
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) :
    CochainComplex.Plus A :=
  (FilteredObject.Finite.Plus.Forget.cochain A).obj K

/-- The map on bounded-below graded-piece complexes induced by a map of finite filtered
complexes. -/
@[stacks 015W "map on a bounded-below finite filtered graded piece"]
noncomputable abbrev gradedPieceComplexMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) (p : ℤ) :
    gradedPieceComplex K p ⟶ gradedPieceComplex L p :=
  (FilteredObject.Finite.Plus.GradedPiece.cochain A p).map f

/-- The map on underlying bounded-below complexes induced by a map of finite filtered
complexes. -/
@[stacks 015W "map on the underlying bounded-below complex"]
noncomputable abbrev underlyingComplexMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) :
    underlyingComplex K ⟶ underlyingComplex L :=
  (FilteredObject.Finite.Plus.Forget.cochain A).map f

/-- The bounded-below homotopy object underlying the `p`-th graded piece of a finite filtered
complex. -/
@[stacks 015W "homotopy graded piece of a bounded-below finite filtered complex"]
noncomputable abbrev gradedPieceSource
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) (p : ℤ) :
    HomotopyCategory.Plus A :=
  (FilteredObject.Finite.Plus.GradedPiece.homotopy A p).obj K

/-- The bounded-below homotopy object obtained by forgetting the finite filtration. -/
@[stacks 015W "underlying bounded-below homotopy complex of a finite filtered complex"]
noncomputable abbrev underlyingSource
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) :
    HomotopyCategory.Plus A :=
  (FilteredObject.Finite.Plus.Forget.homotopy A).obj K

/-- The map on bounded-below graded-piece homotopy objects induced by a map of finite filtered
complexes. -/
@[stacks 015W "map on a bounded-below finite filtered homotopy graded piece"]
noncomputable abbrev gradedPieceSourceMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) (p : ℤ) :
    gradedPieceSource K p ⟶ gradedPieceSource L p :=
  (FilteredObject.Finite.Plus.GradedPiece.homotopy A p).map f

/-- The map on underlying bounded-below homotopy objects induced by a map of finite filtered
complexes. -/
@[stacks 015W "map on the underlying bounded-below homotopy complex"]
noncomputable abbrev underlyingSourceMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) :
    underlyingSource K ⟶ underlyingSource L :=
  (FilteredObject.Finite.Plus.Forget.homotopy A).map f

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
