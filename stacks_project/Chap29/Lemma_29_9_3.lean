/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Point
import StacksCheckRecall

open CategoryTheory Limits
open AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}}
variable (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)

/- Lemma 29.9.3: prescribed points lift to the fiber product if and only if they lie over the
same point of the base. -/
@[stacks 0495] #check
  (AlgebraicGeometry.Scheme.Pullback.exists_point_iff f g x y :
    (∃ z : (pullback f g : Scheme), pullback.fst f g z = x ∧ pullback.snd f g z = y) ↔
      f x = g y)
