/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Differentials
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- With composability s(a)=t(b), the source pullback corrects the target pullback
printed in Stacks 04R9. The target-relative differentials are unchanged.

Lemma 40.4.1 (1): for a groupoid scheme, the canonical morphism
`s^* C_{U/R} ⟶ Ω_t` is an epimorphism. -/
@[stacks 04R9] #check
  (AlgebraicGeometry.GroupoidScheme.Differentials.conormalComparison_epi :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      CategoryTheory.Epi
        (AlgebraicGeometry.GroupoidScheme.Differentials.conormalComparison G))

/- Lemma 40.4.1 (2): if the source map is flat, the canonical morphism
`s^* C_{U/R} ⟶ Ω_t` is an isomorphism. -/
@[stacks 04R9] #check
  (AlgebraicGeometry.GroupoidScheme.Differentials.conormalComparison_isIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      [AlgebraicGeometry.Flat G.s.left],
      CategoryTheory.IsIso
        (AlgebraicGeometry.GroupoidScheme.Differentials.conormalComparison G))
