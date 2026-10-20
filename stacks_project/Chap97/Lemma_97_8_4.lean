/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Algebraic
import StacksCheckRecall

/-!
# Diagonals of algebraic morphisms of stacks in groupoids

If a 1-morphism of stacks in groupoids over `(Sch/S)_fppf` is algebraic and the
target diagonal is representable by algebraic spaces, then the source diagonal
is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 97.8.4: Let `S` be a scheme. Let `F : X ⟶ Y` be a 1-morphism of
stacks in groupoids over `(Sch/S)_fppf`. If `F` is algebraic and
`Δ : Y ⟶ Y × Y` is representable by algebraic spaces, then
`Δ : X ⟶ X × X` is representable by algebraic spaces. -/
@[stacks 0D3R] #check
  (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.diagonal_of_algebraic :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) [Algebraic F],
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y) →
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))

end AlgebraicGeometry
