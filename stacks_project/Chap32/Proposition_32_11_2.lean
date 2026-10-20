/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyClosed.AffineDescent
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Proposition 32.11.2: let `f : X ⟶ S` be a morphism of schemes. If `X` is affine and `f` is
surjective and universally closed, then `S` is affine. -/
@[stacks 05YU] #check
  (AlgebraicGeometry.Scheme.isAffine_of_surjective_universallyClosed :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [UniversallyClosed f] [IsAffine X],
      IsAffine S)
