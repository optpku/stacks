/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Subset
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

variable {k : Type u} [Field k]
variable (X Y : Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
variable (A : Set X.left) (B : Set Y.left)

/- Lemma 33.24.1: for schemes `X`, `Y` over a field `k` and subsets `A ⊆ X`, `B ⊆ Y`,
the pullback subset with projections in `closure A` and `closure B` equals the closure of the
pullback subset with projections in `A` and `B`. -/
@[stacks 047B]
#check
  (AlgebraicGeometry.Scheme.Pullback.subset_closure_eq_closure_subset
      X.hom Y.hom A B :
    AlgebraicGeometry.Scheme.Pullback.subset X.hom Y.hom (closure A) (closure B) =
      closure (AlgebraicGeometry.Scheme.Pullback.subset X.hom Y.hom A B))
