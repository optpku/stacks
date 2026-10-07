module

public import ReasLib.AlgebraicGeometry.Curve.Hyperelliptic
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.22.5: if `k` is a field of characteristic not `2` and
`t : Fin n → k` is injective with `n ≥ 3` odd, then the class group
`CommRing.Pic` of the affine hyperelliptic ring
`k[x, y] / (y ^ 2 - ∏ i, (x - t i))` is nontrivial. -/
@[stacks 078S] #check (AffineHyperelliptic.pic_nontrivial :
  ∀ {k : Type u} [Field k], ringChar k ≠ 2 →
    ∀ {n : ℕ}, 3 ≤ n → Odd n → ∀ (t : Fin n → k), Function.Injective t →
      Nontrivial (CommRing.Pic (AffineHyperelliptic.CoordinateRing t)))
