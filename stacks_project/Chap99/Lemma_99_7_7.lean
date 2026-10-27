/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Limit
import StacksCheckRecall

/-!
# Lemma 99.7.7

In Situation 99.7.1, if `f` is quasi-compact and quasi-separated and `F` is of
finite presentation, then `Q^{fp}_{F/X/B}` preserves directed inverse limits of
affine schemes over `B`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 99.7.7: The finitely presented quotient functor preserves directed inverse limits
of affine schemes over the base. -/
@[stacks 082Q] #check
  (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor_preservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
      [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f] (F : X.Modules)
      [F.IsQuasicoherent] [F.IsFinitePresentation],
      AlgebraicGeometry.AlgebraicSpace.SchemeOver.PreservesDirectedAffineLimits B
        (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor f F))
