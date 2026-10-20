module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 76.51.1: for a commutative square of algebraic spaces over a scheme `S`,
if `Y' ⟶ B'` and `Z' ⟶ X'` are flat, then after base change along `B ⟶ B'` the
fibre product `X ×_B Y` and `Z'` are Tor independent over `X' ×_{B'} Y'`. -/
@[stacks 0CTQ] #check
  (AlgebraicGeometry.AlgebraicSpace.TorIndependentOver.baseChangeProduct_of_flat :
    ∀ {S : Scheme.{u}} {Z' Y' X' B' B : AlgebraicSpace S}
      (i : Z' ⟶ Y') (g : Z' ⟶ X') (q : Y' ⟶ B') (p : X' ⟶ B') (s : B ⟶ B')
      [Flat q] [Flat g] (sq : CommSq i g q p),
      AlgebraicSpace.TorIndependentOver
        (Over.mk
          (pullback.map (pullback.snd p s) (pullback.snd q s) p q
            (pullback.fst p s) (pullback.fst q s) s
            pullback.condition.symm pullback.condition.symm))
        (Over.mk (pullback.lift g i sq.w.symm)))
