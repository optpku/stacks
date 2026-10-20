/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.StrictlyPerfect.Closed
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/- Lemma 20.50.3 (1): if `p : ExactPairing F G`, then `F` is locally strictly perfect. -/
@[stacks 0FPA "(1)"]
#check fun {F G : _root_.CochainComplex (Modules X) ℤ} (p : ExactPairing F G) ↦
  IsLocallyStrictlyPerfect.ofExactPairing p

section Closed

/- Lemma 20.50.3 (2): the chosen second object in `ExactPairing F G` is canonically
isomorphic to the closed-monoidal dual of `F`. -/
@[stacks 0FPA "(2)"]
#check fun {F G : _root_.CochainComplex (Modules X) ℤ} (p : ExactPairing F G) ↦
  MonoidalClosed.Dual.rightDualIso p

end Closed

/- The two directions form a reusable object-property characterization. -/
#check @isLocallyStrictlyPerfect_iff_isRightDualizable

end AlgebraicGeometry.RingedSpace.CochainComplex
