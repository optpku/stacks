module

public import stacks_project.Chap66.Lemma_66_4_12_UniqueIso
public import stacks_project.Chap68.Lemma_68_4_3_Fibre
public import stacks_project.Chap68.Lemma_68_12_8_Decent
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.11.1 (1): let `S` be a scheme. Let `X` be an algebraic space over `S`.
The assignment sending a monomorphism `Spec(k) ⟶ X`, with `k` a field, to its
class in `|X|` is always injective. -/
@[stacks 03K4] #check
  (FieldValuedPoint.iso_unique_of_mono :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {p q : FieldValuedPoint X}
      [Mono p.hom] [Mono q.hom],
      Points.mk p = Points.mk q →
        Nonempty (p.Factorization q) ∧ Subsingleton (p.Factorization q))

namespace AlgebraicGeometry.AlgebraicSpace.existsMonoFieldValuedPoint

/-- Lemma 68.11.1 (2): let `S` be a scheme. Let `X` be a decent algebraic space
over `S`. Every point of `|X|` arises from a monomorphism `Spec(k) ⟶ X` with
`k` a field. Combined with unique factorization of such monomorphisms, this
assignment is bijective. -/
@[stacks 03K4]
theorem of_isDecent {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) : existsMonoFieldValuedPoint X x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.existsMonoFieldValuedPoint
