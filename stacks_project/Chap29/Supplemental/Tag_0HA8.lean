/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Excellent
import StacksCheckRecall

/-!
# Characterization of quasi-excellent schemes

A scheme is quasi-excellent if and only if it is a G-scheme and J-2.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma [Stacks 0HA8]: a scheme is quasi-excellent if and only if it is a G-scheme and J-2. -/
@[stacks 0HA8] #check (AlgebraicGeometry.Scheme.quasiExcellent_iff_gScheme_isJ2 :
  ∀ X : Scheme.{u}, X.QuasiExcellent ↔ X.GScheme ∧ X.IsJ2)
