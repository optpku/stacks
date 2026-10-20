/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.DenseOpen
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.45.2: every quasi-finite morphism of schemes is finite after restriction over
some dense open subset of its target. -/
@[stacks 03I1] #check
  (AlgebraicGeometry.Scheme.Hom.exists_dense_open_isFinite_restrict_of_quasiFinite :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [AlgebraicGeometry.Scheme.Hom.QuasiFinite f],
      ∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (f ∣_ U))
