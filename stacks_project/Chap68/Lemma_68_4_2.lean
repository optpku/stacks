/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteFibers

/-!
# Finite étale fibres over a point of an algebraic space

Existence of an étale scheme covering with finite fibres over a point is
equivalent to the affine étale finite-fibre test.
-/

universe u

/- Lemma 68.4.2: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`x` be a point of `|X|`. The following are equivalent: there exists a family of
schemes `U i` and étale morphisms `φ i : ofOver (U i) ⟶ X` such that
`∐ φ i : ∐ U i ⟶ X` is surjective, and such that for each `i` the fibre of
`|U i| → |X|` over `x` is finite; and for every affine scheme `U` and étale
morphism `φ : ofOver U ⟶ X` the fibre of `|U| → |X|` over `x` is finite. -/
@[stacks 03JS] #check (AlgebraicGeometry.AlgebraicSpace.existsEtaleCoverFiniteFibre_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    AlgebraicGeometry.AlgebraicSpace.existsEtaleCoverFiniteFibre X x ↔
      AlgebraicGeometry.AlgebraicSpace.forallAffineEtaleFiniteFibre X x)
