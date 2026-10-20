/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.DimensionTwo
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.QuasiProjective

/- Lemma 54.16.10: for a Noetherian scheme `S`, a separated finite-type morphism
`f : X ⟶ S` with regular source of topological Krull dimension `2` is quasi-projective. -/
@[stacks 0C5N] #check (AlgebraicGeometry.QuasiProjective.instOfRegularDimensionTwo :
    ∀ {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsSeparated f]
      [Scheme.Hom.FiniteType f] [Scheme.Regular X],
      topologicalKrullDim X = 2 → QuasiProjective f)

end AlgebraicGeometry.QuasiProjective
