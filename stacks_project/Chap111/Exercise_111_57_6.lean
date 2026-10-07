module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PowerSum
import StacksCheckRecall

/-!
# Exercise 111.57.6

Classification of pairs `(n, p)` for which the power-sum closed subscheme
`X ⊂ P^n_k` is singular.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Exercise 111.57.6: let `k` be a field of characteristic `p > 0` different
from `2` and `3`, and let `X ⊂ P^n_k` be the closed subscheme cut out by
`psum (Fin (n + 1)) k 1`, `psum (Fin (n + 1)) k 2`, and
`psum (Fin (n + 1)) k 3`. Then `X` is singular if and only if `p ≤ n + 1`. -/
@[stacks 0AAS] #check (AlgebraicGeometry.ProjectiveSpace.PowerSum.singular_iff :
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] (n : ℕ)
    (hp : 0 < p) (h2 : p ≠ 2) (h3 : p ≠ 3),
    ¬ AlgebraicGeometry.Scheme.Regular
      (AlgebraicGeometry.ProjectiveSpace.PowerSum.scheme k n) ↔ p ≤ n + 1)

/- Under the same characteristic hypotheses, `Sing(scheme k n)` is nonempty if
and only if `p ≤ n + 1`. -/
#check (AlgebraicGeometry.ProjectiveSpace.PowerSum.singularLocus_nonempty_iff :
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] (n : ℕ)
    (hp : 0 < p) (h2 : p ≠ 2) (h3 : p ≠ 3),
    (Sing(AlgebraicGeometry.ProjectiveSpace.PowerSum.scheme k n)).Nonempty ↔ p ≤ n + 1)
