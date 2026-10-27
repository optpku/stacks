/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Excellent.Permanence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

/- Lemma (0HA9): A quasi-excellent scheme is Nagata. -/
@[stacks 0HA9] #check
  (AlgebraicGeometry.Scheme.nagata_of_quasiExcellent : ∀ (X : Scheme.{u}) [Scheme.QuasiExcellent X],
    Scheme.Nagata X)
