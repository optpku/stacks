/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.DimensionTwo
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Projective

/- Lemma 54.16.11: if `S` is Noetherian and `f : X ⟶ S` is proper with `X` regular of
topological Krull dimension `2`, then `f` is projective over `S`. -/
@[stacks 0C5P] #check (AlgebraicGeometry.Projective.instOfProperRegularDimensionTwo :
    ∀ {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] [Scheme.Regular X],
      topologicalKrullDim X = 2 → Projective f)

end AlgebraicGeometry.Projective
