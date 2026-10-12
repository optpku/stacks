/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 33.20.5 (1): For locally algebraic schemes over a field, the local dimension of their
product at a point is the sum of the local dimensions at its two projections. -/
@[stacks 0B2M]
#check (AlgebraicGeometry.SchemeOverField.topologicalKrullDimAt_pullback_eq_add :
  ∀ {k : Type u} [Field k] (X Y : AlgebraicGeometry.SchemeOverField k)
    [AlgebraicGeometry.LocallyAlgebraic X] [AlgebraicGeometry.LocallyAlgebraic Y]
    (z : (pullback X.hom Y.hom : AlgebraicGeometry.Scheme)),
    topologicalKrullDimAt z =
      topologicalKrullDimAt (pullback.fst X.hom Y.hom z) +
        topologicalKrullDimAt (pullback.snd X.hom Y.hom z))

/- Lemma 33.20.5 (2): The dimension of a product of locally algebraic schemes over a field is the
sum of their dimensions. -/
@[stacks 0B2M]
#check (AlgebraicGeometry.SchemeOverField.topologicalKrullDim_pullback_eq_add :
  ∀ {k : Type u} [Field k] (X Y : AlgebraicGeometry.SchemeOverField k)
    [AlgebraicGeometry.LocallyAlgebraic X] [AlgebraicGeometry.LocallyAlgebraic Y],
    topologicalKrullDim (pullback X.hom Y.hom : AlgebraicGeometry.Scheme) =
      topologicalKrullDim X.left + topologicalKrullDim Y.left)
