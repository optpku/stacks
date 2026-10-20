/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Diagonal
import StacksCheckRecall

/-!
# Completing the relative diagonal along a closed subset

The fibre product of completions is the completion of the fibre product,
and its relative diagonal is the restriction of the original relative diagonal.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits TopologicalSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.isPullback_completionAlong_fibreProduct :
  ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X) (T : Closeds (Points X)),
    IsPullback (completionAlong.fibreProductFst f T) (completionAlong.fibreProductSnd f T)
      (completionAlong.map f T) (completionAlong.map f T))

/- Remark 88.23.6: the relative diagonal of the completed morphism is the
completion of the relative diagonal, under the canonical fibre-product comparison. -/
@[stacks 0GDF] #check (AlgebraicGeometry.AlgebraicSpace.completionAlong_diagonal :
  ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X) (T : Closeds (Points X)),
    completionAlong.diagonalMap f T ≫
        (AlgebraicGeometry.AlgebraicSpace.isPullback_completionAlong_fibreProduct f T).isoPullback.hom =
      pullback.diagonal (completionAlong.map f T))
