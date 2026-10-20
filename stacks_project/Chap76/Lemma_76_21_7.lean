/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale.NaiveCotangent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 76.21.7: a scheme morphism is formally étale exactly when the degree `-1`
and degree `0` homology objects of its naive cotangent complex are zero. -/
@[stacks 0D11]
#check
  (AlgebraicGeometry.FormallyEtale.iff_naiveCotangent :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      FormallyEtale f ↔
        IsZero ((NL[f.toShHom]).homology (-1)) ∧
          IsZero ((NL[f.toShHom]).homology 0))
