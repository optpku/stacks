/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization

@[expose] public section

universe u

/- Definition 33.39.7: Let `k` be a field, let `X` be a locally algebraic
`k`-scheme, and let `x ∈ X` have reduced, one-dimensional stalk. The
pointwise `δ`-invariant of `X` at `x` is the normalization `δ`-invariant of
the stalk. -/
@[stacks 0C1T] #check
  (AlgebraicGeometry.SchemeOverField.deltaInvariantAt :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      (x : X.left), ℕ∞)

#check (AlgebraicGeometry.SchemeOverField.deltaInvariantAt_def :
  ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    (x : X.left),
    AlgebraicGeometry.SchemeOverField.deltaInvariantAt X x =
      Normalization.deltaInvariant (AlgebraicGeometry.SchemeOverField.stalkRing X x))

#check (AlgebraicGeometry.SchemeOverField.instNagataRingStalkOfLocallyAlgebraic :
  ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [AlgebraicGeometry.LocallyAlgebraic X] (x : X.left),
    NagataRing (AlgebraicGeometry.SchemeOverField.stalkRing X x))
