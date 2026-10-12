/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Unique factorization through monomorphic field-valued points

A monomorphism `Spec(K) ⟶ X` from the spectrum of a field is a unique-factorization
representative of its point of `|X|`: any other field-valued representative factors
uniquely through it.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint

/-- A field-valued point representing the same point as a monomorphic field-valued point
factors uniquely through it. -/
theorem unique_factorization_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} [Mono p.hom] (h : Points.mk p = Points.mk q) :
    Nonempty (q.Factorization p) ∧ Subsingleton (q.Factorization p) :=
  sorry

/-- A field-valued point representing the same point as a monomorphic field-valued point
factors through it. -/
theorem exists_factorization_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} [Mono p.hom] (h : Points.mk p = Points.mk q) :
    Nonempty (q.Factorization p) :=
  sorry

/-- Factorizations of a field-valued point through a monomorphism are unique. -/
theorem Factorization.subsingleton_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} [Mono p.hom] :
    Subsingleton (q.Factorization p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint
