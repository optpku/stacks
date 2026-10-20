/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable.EtaleCover
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 68.4.6: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
The following are equivalent: there exist schemes `U i` and étale morphisms
`φ i : ofOver (U i) ⟶ X` such that `∐ φ i : ∐ U i ⟶ X` is surjective and each
`U i ⟶ X` has universally bounded fibres; and for every affine scheme `U` and
étale morphism `φ : ofOver U ⟶ X` the fibres of `U ⟶ X` are universally
bounded. The covering family is arbitrary, with a separate universal fibre bound
for each member. `IsReasonable X` is precisely the condition that every affine
étale scheme morphism into `X` has universally bounded fibres. -/
@[stacks 03JT] #check
  (AlgebraicGeometry.AlgebraicSpace.existsEtaleCoverUniversallyBoundedFibres_iff_isReasonable :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      AlgebraicGeometry.AlgebraicSpace.existsEtaleCoverUniversallyBoundedFibres X ↔
        AlgebraicGeometry.AlgebraicSpace.IsReasonable X)
