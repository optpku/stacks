/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint.BaseChange
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory Limits

universe u

/- Lemma 29.20.4: let `f : X ⟶ S` be locally of finite type and let `g : S' ⟶ S` be any
morphism. For a point `x'` of the base change `X ×[S] S'`, if its image in `X` is closed in
the corresponding fibre of `f`, then `x'` is closed in its fibre under the base-changed
morphism. -/
@[stacks 053M] #check
  (AlgebraicGeometry.asFiber_mem_closedPoints_of_pullback_snd :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
      (x' : (pullback f g : Scheme))
      (_ :
        f.asFiber (pullback.fst f g x') ∈
          closedPoints (f.fiber (f (pullback.fst f g x')))),
      (pullback.snd f g).asFiber x' ∈
        closedPoints ((pullback.snd f g).fiber ((pullback.snd f g) x')))
