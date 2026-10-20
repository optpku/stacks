/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong.AffineTypes
import StacksCheckRecall

/-!
# Recompletion of an affine formal algebraic space

If `X` is an affine formal algebraic space, then its completion along a closed
subset of the reduction remains an affine formal algebraic space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace (Points)
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.37.1: Let `S` be a scheme and `X` an affine formal algebraic space
 over `S`, including the directed affine thickening presentation and the
 representable coequalizer size condition. For any closed subset `T` of its
 reduction, the completion subfunctor of sections `f` with `f(|U|) ⊆ T` is
 again an affine formal algebraic space. -/
@[stacks 0GVQ] #check (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.isAffine :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    (R : ReductionData X) (T : Closeds (Points R.space)),
    AffineFormalAlgebraicSpace.IsAffine (Recompletion.functor R T))
