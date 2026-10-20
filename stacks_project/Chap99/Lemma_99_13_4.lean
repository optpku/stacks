/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Over.Equivalence
import StacksCheckRecall

/-!
# Lemma 99.13.4

The groupoid of finite-type morphisms of algebraic spaces into an algebraic
space `T` is equivalent to the category of based functors from the associated
stack `S_T` to `Spaces'_ft`, and likewise for finite-presentation, flat, and
proper morphisms versus `Spaces'_{fp, flat, proper}`. The source states this
over `Spec ℤ`; the declarations are relative to a general base scheme `S`.
-/

universe u

/- Lemma 99.13.4 (1): The canonical base-change functor classifies finite-type
algebraic spaces over an algebraic space. -/
@[stacks 0E93] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.FtOver.yoneda.instIsEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (T : AlgebraicGeometry.AlgebraicSpace S),
      (AlgebraicGeometry.AlgebraicSpace.Spaces.FtOver.yoneda T).IsEquivalence)

/- Lemma 99.13.4 (2): The canonical base-change functor classifies
finite-presentation, flat, proper algebraic spaces over an algebraic space. -/
@[stacks 0E93] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperOver.yoneda.instIsEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (T : AlgebraicGeometry.AlgebraicSpace S),
      (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperOver.yoneda T).IsEquivalence)
