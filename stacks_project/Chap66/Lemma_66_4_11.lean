/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_11_Factorization
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
  (FieldValuedPoint.unique_factorization_of_mono :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {p q : FieldValuedPoint X} [Mono p.hom],
      Points.mk p = Points.mk q →
        Nonempty (q.Factorization p) ∧ Subsingleton (q.Factorization p))
