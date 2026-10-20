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
open scoped AlgebraicGeometry

universe u

/- Lemma 30.13.3

Let `f : Y ⟶ X` be a finite surjective morphism of schemes. If `Y` is affine and `X` is
Noetherian, then `X` is affine.
-/
@[stacks 01YQ] #check
  (AlgebraicGeometry.Scheme.isAffine_target_of_isFinite_surjective :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsAffine Y]
      [IsNoetherian X], IsAffine X)
