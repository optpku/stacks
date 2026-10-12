/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section

noncomputable section

universe u

namespace MvPolynomial.ReduciblePlanes

/-- The relation ideal `(x z, x w, y z, y w)` in `k[x, y, z, w]`, with
`X 0`, `X 1`, `X 2`, `X 3` corresponding to `x`, `y`, `z`, `w`. -/
def relationIdeal (k : Type u) [Field k] : Ideal (MvPolynomial (Fin 4) k) :=
  Ideal.span {X 0 * X 2, X 0 * X 3, X 1 * X 2, X 1 * X 3}

/-- `relationIdeal k` is the span of `X 0 * X 2`, `X 0 * X 3`, `X 1 * X 2`, and
`X 1 * X 3`. -/
theorem relationIdeal_eq_span (k : Type u) [Field k] :
    relationIdeal k =
      Ideal.span {X 0 * X 2, X 0 * X 3, X 1 * X 2, X 1 * X 3} := sorry

/-- The coordinate ring of the union of the planes `V(x, y)` and `V(z, w)`. -/
abbrev Ring (k : Type u) [Field k] :=
  MvPolynomial (Fin 4) k ⧸ relationIdeal k

/-- The irrelevant ideal `(x, y, z, w)` in the union of two coordinate planes. -/
def irrelevantIdeal (k : Type u) [Field k] : Ideal (Ring k) :=
  Ideal.map (Ideal.Quotient.mk (relationIdeal k))
    (Ideal.span {X 0, X 1, X 2, X 3})

/-- `irrelevantIdeal k` is the image of `Ideal.span {X 0, X 1, X 2, X 3}` in
`Ring k`. -/
theorem irrelevantIdeal_eq_map (k : Type u) [Field k] :
    irrelevantIdeal k =
      Ideal.map (Ideal.Quotient.mk (relationIdeal k))
        (Ideal.span {X 0, X 1, X 2, X 3}) := sorry

/-- Over any field, the coordinate ring of the union of two coordinate planes has
depth `1` with respect to its irrelevant ideal. -/
theorem depth_irrelevant (k : Type u) [Field k] :
    Ideal.depth (irrelevantIdeal k) (Ring k) = 1 := sorry

end MvPolynomial.ReduciblePlanes
