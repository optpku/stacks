/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Blowup.Normalized
import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence

open AlgebraicGeometry TopologicalSpace

universe u

/- Definition 54.14.2: a two-dimensional Noetherian integral scheme has a resolution of
singularities by normalized blowups if its normalization is followed by a finite sequence of
normalized blowups at closed points, every stage is proper over the original scheme, and the
terminal scheme is regular. -/
@[stacks 0BGL] #check (AlgebraicGeometry.Scheme.HasResolutionByNormalizedBlowups :
  ∀ (Y : Scheme.{u}) [IsNoetherian Y] [IsIntegral Y], topologicalKrullDim Y = 2 → Prop)
