module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism

/-!
# Unique factorization through monomorphic field-valued points

A monomorphism `Spec(K) ⟶ X` from the spectrum of a field is a unique-factorization
representative of its point of `|X|`: any other field-valued representative factors
uniquely through it.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.unique_factorization_of_mono :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {q p : FieldValuedPoint X},
      Mono p.hom → Points.mk q = Points.mk p →
        Nonempty (q.Factorization p) ∧ Subsingleton (q.Factorization p))
