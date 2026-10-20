/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Diagonal.SecondDiagonal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

universe u

/- Lemma 97.4.4: The second diagonal of a category fibred in groupoids over
`(Sch/S)_fppf` is representable by algebraic spaces if and only if every
scheme-slice base change of its first diagonal has diagonal representable by
algebraic spaces. -/
@[stacks 07WG] #check
  (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.secondDiagonal_iff :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    relativelyRepresentableByAlgebraicSpaces
        (Hom.diagonal.{u + 1, u, u + 1}
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)) ↔
      ∀ {V : Over S}
        (φ : GroupoidsOver.slice V ⟶
          TwoFibreProduct.apex.{u + 1, u, u + 1, u}
            X.baseProjection X.baseProjection),
        relativelyRepresentableByAlgebraicSpaces
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
            (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
              (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) φ)))
