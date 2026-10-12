/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Power
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.26.2: an invertible module on a scheme is ample if and only if any positive tensor
power is ample. -/
@[stacks 01PT] #check
  (@AlgebraicGeometry.Scheme.Modules.isAmple_iff_tensorPow_isAmple :
    ∀ {X : Scheme.{u}} (L : X.Modules) [hL : Scheme.Modules.Invertible L] (n : ℕ), 0 < n →
      (Scheme.Modules.IsAmple L ↔
        @Scheme.Modules.IsAmple X (RingedSpace.TensorPower.sheaf L n)
          (Scheme.Modules.Invertible.tensorPower_isInvertible hL n)))
