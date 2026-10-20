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

/- Remark 29.51.3: a quasi-finite morphism of schemes is finite over a dense open subset of
the target. -/
@[stacks 03HZ] #check
  (AlgebraicGeometry.Scheme.Hom.exists_dense_open_isFinite_restrict_of_quasiFinite :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Scheme.Hom.QuasiFinite f],
      ∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (f ∣_ U))
