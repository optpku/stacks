module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AffineScheme.Hypersurface

universe u

/- Exercise 111.66.4: for a field `k` and a nonconstant polynomial `f` in
`k[x_1, …, x_n]`, the affine hypersurface `X = Spec (k[x_1, …, x_n] ⧸ (f))` is a
variety over `k` if and only if `f` is irreducible. -/
@[stacks 0H8T] #check
  (AlgebraicGeometry.AffineHypersurface.variety_iff_irreducible :
    ∀ {k : Type u} [Field k] {n : ℕ} {f : MvPolynomial (Fin n) k},
      f.totalDegree ≠ 0 →
        (AlgebraicGeometry.Variety (AlgebraicGeometry.AffineHypersurface.over f) ↔
          Irreducible f))
