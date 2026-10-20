/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism

/-!
# Comparison of thickenings of algebraic stacks

A thickening of algebraic stacks is equivalent to a morphism representable by
algebraic spaces that is a thickening on scheme-slice representing morphisms.
Such a morphism is a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening

/-- A morphism of algebraic stacks is a thickening if and only if it is
representable by algebraic spaces and has the algebraic-space thickening
property in the sense of scheme-slice tests. -/
theorem iff_has {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') :
    IsThickening i ↔ relativelyRepresentableByAlgebraicSpaces i ∧
      has (@AlgebraicSpace.IsThickening S) i := sorry

/-- A 1-morphism of algebraic stacks which is representable by algebraic spaces
and has the algebraic-space thickening property is a thickening. -/
theorem of_has {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    (hf : relativelyRepresentableByAlgebraicSpaces i)
    (h : has (@AlgebraicSpace.IsThickening S) i) : IsThickening i :=
  (iff_has i).mpr ⟨hf, h⟩

/-- A thickening of algebraic stacks has the algebraic-space thickening
property on scheme-slice representing morphisms. -/
theorem has_isThickening {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    has (@AlgebraicSpace.IsThickening S) i :=
  ((iff_has i).mp inferInstance).2

/-- A thickening of algebraic stacks is a universal homeomorphism. -/
instance instUniversalHomeomorphism {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    UniversalHomeomorphism i := sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening
