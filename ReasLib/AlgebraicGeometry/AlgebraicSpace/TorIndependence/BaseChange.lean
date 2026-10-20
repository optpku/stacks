module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentOver

/-- For a commutative square of algebraic spaces over a scheme, if `Y' ⟶ B'` and
`Z' ⟶ X'` are flat, then after any base change `B ⟶ B'` the product of the base
changes of `X'` and `Y'` over `B` and `Z'` are Tor independent over `X' ×_{B'} Y'`,
via the canonical comparison and cone morphisms. -/
theorem baseChangeProduct_of_flat {S : Scheme.{u}} {Z' Y' X' B' B : AlgebraicSpace S}
    (i : Z' ⟶ Y') (g : Z' ⟶ X') (q : Y' ⟶ B') (p : X' ⟶ B') (s : B ⟶ B')
    [Flat q] [Flat g] (sq : CommSq i g q p) :
    AlgebraicSpace.TorIndependentOver
      (Over.mk
        (pullback.map (pullback.snd p s) (pullback.snd q s) p q
          (pullback.fst p s) (pullback.fst q s) s
          pullback.condition.symm pullback.condition.symm))
      (Over.mk (pullback.lift g i sq.w.symm)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentOver
