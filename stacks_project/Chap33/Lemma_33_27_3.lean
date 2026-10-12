/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.Relative

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.27.3: let `k` be a field, let `f : Y ⟶ X` be a quasi-compact morphism of locally
algebraic schemes over `k`, and let `X'` be the normalization of `X` in `Y`. If `Y` is reduced,
then the canonical normalization morphism `X' ⟶ X`, formalized as `f.left.fromNormalization`,
is finite. -/
@[stacks 0BXS] #check
  (AlgebraicGeometry.SchemeOverField.RelativeNormalization.instIsFiniteFromNormalization :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} (f : Y ⟶ X)
      [QuasiCompact f.left] [LocallyAlgebraic X] [LocallyAlgebraic Y] [IsReduced Y.left],
      IsFinite f.left.fromNormalization)
