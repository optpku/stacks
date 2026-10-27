/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Limits

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

@[expose] public section

universe u v w

/- Lemma 60.8.2 (1): the relative crystalline category has all finite nonempty limits,
including binary products and pullbacks. -/
@[stacks 07I9]
#check (AlgebraicGeometry.Scheme.Crystalline.Base.hasFiniteNonemptyLimits :
    ∀ {p : ℕ} [Fact p.Prime] (B : AlgebraicGeometry.Scheme.Crystalline.Base.{u} p),
      HasFiniteNonemptyLimits
        (RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed))

/- Lemma 60.8.2 (2): the source-forgetting functor preserves all existing limits. -/
@[stacks 07I9]
#check (AlgebraicGeometry.Scheme.Crystalline.Base.forgetful_preservesLimits :
    ∀ {p : ℕ} [Fact p.Prime] (B : AlgebraicGeometry.Scheme.Crystalline.Base.{u} p),
      PreservesLimitsOfSize.{v, w}
        (crystallineForgetful B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.source B.sourceToClosed B.prime_nilpotent))
