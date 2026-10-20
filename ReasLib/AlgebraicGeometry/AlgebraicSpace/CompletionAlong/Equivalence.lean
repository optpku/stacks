/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Functor

/-!
# Equivalence induced by completion along a closed subset
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a locally Noetherian algebraic space, completion along a closed subset
is an equivalence from locally of finite type morphisms that are isomorphisms
over its open complement to rig-étale morphisms of locally Noetherian formal
algebraic spaces over the completion. -/
@[stacks 0ARB]
instance completionFunctor.instIsEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    (completionFunctor X T).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
