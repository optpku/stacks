/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.AffineDescent
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 32.11.1: Let `f : X ⟶ S` be a surjective finite morphism of schemes. If `X` is
affine, then `S` is affine. -/
@[stacks 01ZT] #check
  (AlgebraicGeometry.Scheme.isAffine_of_isFinite_surjective :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [IsFinite f] [IsAffine X], IsAffine S)
