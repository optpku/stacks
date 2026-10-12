/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Category.ModuleCat.Ext.MvPolynomial

@[expose] public section

universe u

/- Exercise 111.11.2 (1): for a field `k` and `R = MvPolynomial (Fin 2) k`, the displayed
augmented Koszul sequence `0 ⟶ R ⟶ R ⊕ 2 ⟶ R ⟶ k ⟶ 0` with maps `(y; -x)`, `(x, y)`, and
evaluation at the origin is exact. -/
@[stacks 0CRD] #check
  (MvPolynomial.augmentedKoszulXY_acyclic :
    ∀ (k : Type u) [Field k], (MvPolynomial.augmentedKoszulXY k).Acyclic)

/- Exercise 111.11.2 (2): writing `k = R ⧸ (x, y)` as an `R`-module for
`R = MvPolynomial (Fin 2) k`, the `k`-dimension of `Ext^i_R(k, k)` is `Nat.choose 2 i`. -/
@[stacks 0CRD] #check
  (MvPolynomial.ext_finrank_quotient_span_XY :
    ∀ (k : Type u) [Field k] (i : ℕ),
      Module.finrank k
        (CategoryTheory.Abelian.Ext
          (ModuleCat.of (MvPolynomial (Fin 2) k) (MvPolynomial.quotientSpanXY k))
          (ModuleCat.of (MvPolynomial (Fin 2) k) (MvPolynomial.quotientSpanXY k)) i) =
        Nat.choose 2 i)
