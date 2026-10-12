/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.69.1: for a commutative square of schemes and a base change, if
`Y' ⟶ S'` and `Z' ⟶ X'` are flat, then the base-changed product and `Z'` are Tor
independent over `X' ×[S'] Y'`. -/
@[stacks 0CTA] #check
  (AlgebraicGeometry.Scheme.TorIndependentOver.baseChangeProduct_of_flat :
    ∀ {Z' Y' X' S' S : Scheme.{u}}
      (i : Z' ⟶ Y') (g : Z' ⟶ X') (q : Y' ⟶ S') (p : X' ⟶ S') (s : S ⟶ S')
      [Flat q] [Flat g] (sq : CommSq i g q p),
      AlgebraicGeometry.Scheme.TorIndependentOver
        (Over.mk
          (pullback.map (pullback.snd p s) (pullback.snd q s) p q
            (pullback.fst p s) (pullback.fst q s) s
            pullback.condition.symm pullback.condition.symm))
        (Over.mk (pullback.lift g i sq.w.symm)))
