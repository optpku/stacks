/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.4.11: let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`p : Spec(K) ⟶ X` and `q : Spec(L) ⟶ X` be morphisms where `K` and `L` are fields.
Assume `p` and `q` determine the same point of `|X|` and `p` is a monomorphism.
Then `q` factors uniquely through `p`. -/
@[stacks 0H2X] #check
  (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.unique_factorization_of_mono :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {q p : FieldValuedPoint X},
      Mono p.hom → Points.mk q = Points.mk p →
        Nonempty (q.Factorization p) ∧ Subsingleton (q.Factorization p))
