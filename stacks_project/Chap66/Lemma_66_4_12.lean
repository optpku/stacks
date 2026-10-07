module

public import stacks_project.Chap66.Lemma_66_4_12_UniqueIso
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.4.12: let `S` be a scheme. Let `X` be an algebraic space over `S`.
The assignment sending a monomorphism `Spec(k) ⟶ X`, with `k` a field, to its
class in `|X|` is injective. -/
@[stacks 03E1] #check
  (FieldValuedPoint.iso_unique_of_mono :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {p q : FieldValuedPoint X}
      [Mono p.hom] [Mono q.hom],
      Points.mk p = Points.mk q →
        Nonempty (p.Factorization q) ∧ Subsingleton (p.Factorization q))
