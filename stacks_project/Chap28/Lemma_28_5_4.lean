/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Noetherian
import StacksCheckRecall

universe u

/- Lemma 28.5.4: A locally Noetherian scheme is quasi-separated. -/
@[stacks 01OY]
#check (AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}, [AlgebraicGeometry.IsLocallyNoetherian X] →
    QuasiSeparatedSpace X)
