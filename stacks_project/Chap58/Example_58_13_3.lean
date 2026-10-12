/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AffineSpace.QuadraticMonomial

/-!
Purity of the branch locus implies that, for regular `X`, the inertia groups in
Lemma 58.13.2 may be taken at codimension-one points. The quadratic-monomial
double cover shows that in general one cannot restrict to codimension one:
ramification occurs only over a height-`n` origin.
-/

@[expose] public section

open Algebra AlgebraicGeometry.AffineSpace.QuadraticMonomial

universe u v

variable {k : Type u} {ι : Type v} [Field k] [DecidableEq ι] [Fintype ι]

/- Example 58.13.3 (1): the embedding `k[t_i t_j] ⊂ k[t_1,…,t_n]` has degree `2`
as an extension of fraction fields, when `k` is not of characteristic `2`. -/
@[stacks 0BTE] #check
  (AlgebraicGeometry.AffineSpace.QuadraticMonomial.finrank_fraction_quadraticMonomialAdjoin :
    ∀ [Nonempty ι], ringChar k ≠ 2 →
      Module.finrank (FractionRing (quadraticMonomialAdjoin k ι))
        (FractionRing (MvPolynomial ι k)) = 2)

/- Example 58.13.3 (2): the morphism `Y → X` is unramified at every prime of
`k[t_i]` whose contraction is not the origin ideal `m = (t_i t_j)`. -/
@[stacks 0BTE] #check
  (AlgebraicGeometry.AffineSpace.QuadraticMonomial.unramifiedAt_of_ne_origin :
    ∀ [Nonempty ι], ringChar k ≠ 2 → ∀ (q : Ideal (MvPolynomial ι k)) [q.IsPrime],
      q.comap (algebraMap (quadraticMonomialAdjoin k ι) (MvPolynomial ι k)) ≠
        originQuadraticIdeal k ι → IsUnramifiedAt (quadraticMonomialAdjoin k ι) q)

/- Example 58.13.3 (3): the morphism `Y → X` is ramified over the origin
maximal ideal `m = (t_i t_j)`. -/
@[stacks 0BTE] #check
  (AlgebraicGeometry.AffineSpace.QuadraticMonomial.not_unramifiedAt_origin :
    ∀ [Nonempty ι], ringChar k ≠ 2 → ∀ (q : Ideal (MvPolynomial ι k)) [q.IsPrime]
      [q.LiesOver (originQuadraticIdeal k ι)],
      ¬ IsUnramifiedAt (quadraticMonomialAdjoin k ι) q)

/- Example 58.13.3 (4): the origin ideal `m = (t_i t_j)` is maximal of
codimension `n = Fintype.card ι` in `X`. -/
@[stacks 0BTE] #check
  (AlgebraicGeometry.AffineSpace.QuadraticMonomial.height_originQuadraticIdeal :
    (originQuadraticIdeal k ι).IsMaximal ∧
      (originQuadraticIdeal k ι).height = Fintype.card ι)
