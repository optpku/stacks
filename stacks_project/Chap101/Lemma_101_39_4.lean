/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Postcompose
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X' Y' X Y : GroupoidsOver S}
variable [AlgebraicStack X'] [AlgebraicStack Y'] [AlgebraicStack X] [AlgebraicStack Y]
variable {p : X' ⟶ Y'} {q : X' ⟶ X} {g : Y' ⟶ Y} {f : X ⟶ Y}
variable (φ : p ≫ g ≅ q ≫ f)
variable [Bicategory.PseudoPullbackCone.IsBilimit
  (⟨X', q, p, φ.symm⟩ : Bicategory.PseudoPullbackCone f g)]
variable (sq : ValuativeCommSq p)

/- Lemma 101.39.4: in a 2-commutative diagram of algebraic stacks
`Spec(K) —x'→ X' —q→ X` over `Spec(A) —y'→ Y' —g→ Y`, if the right square is
2-cartesian, then postcomposition along that square induces an equivalence
from the dotted-arrow category of the left valuative square to that of the
outer valuative rectangle.

The left dotted-arrow category is `DottedArrow sq.toCone`, with `γ' = sq.iso`.
The outer dotted-arrow category is `DottedArrow (sq.toCone.postcompose φ)`,
with `x = sq.i₁ ≫ q`, `y = sq.i₂ ≫ g`, and `γ = pasteSquareIso sq.iso φ`. -/
@[stacks 0CLE]
#check (CategoryTheory.DottedArrow.postcomposeFunctor.isEquivalence sq.toCone φ :
  (CategoryTheory.DottedArrow.postcomposeFunctor sq.toCone φ).IsEquivalence)

end AlgebraicGeometry.AlgebraicStack
