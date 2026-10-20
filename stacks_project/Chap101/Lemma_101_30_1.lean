/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Spectral
import StacksCheckRecall

/-!
# Spectral spaces of quasi-compact algebraic stacks with quasi-compact diagonal

A quasi-compact algebraic stack whose absolute diagonal is quasi-compact has
spectral space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.30.1: Let `X` be a quasi-compact algebraic stack whose diagonal `Δ`
is quasi-compact. Then `|X|` is a spectral topological space. -/
@[stacks 0DQN] #check
  (AlgebraicGeometry.AlgebraicStack.spectralSpace_of_quasiCompact_diagonal :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiCompact X],
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)) →
      SpectralSpace (Points X))

end AlgebraicGeometry.AlgebraicStack
