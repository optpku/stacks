/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Fiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.44.8: If `f : X ⟶ S` is an integral morphism, then every point of `X` is closed
in its fibre over `S`. -/
@[stacks 02NT] #check
  (AlgebraicGeometry.asFiber_mem_closedPoints_of_isIntegralHom :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsIntegralHom f] (x : X),
      f.asFiber x ∈ closedPoints (f.fiber (f x)))
