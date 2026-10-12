/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Unique isomorphism of monomorphic field-valued points

Two monomorphisms `Spec(k) ⟶ X` from spectra of fields that represent the same
point of `|X|` are uniquely isomorphic over `X`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint

/-- Monomorphic field-valued points representing the same point of `|X|` uniquely
factor through each other. -/
theorem iso_unique_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} [Mono p.hom] [Mono q.hom]
    (h : Points.mk p = Points.mk q) :
    Nonempty (p.Factorization q) ∧ Subsingleton (p.Factorization q) :=
  sorry

/-- Two monomorphic field-valued points determine the same point of `|X|` if and only
if one factors through the other. -/
theorem mk_eq_mk_iff_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} [Mono p.hom] [Mono q.hom] :
    Points.mk p = Points.mk q ↔ Nonempty (p.Factorization q) :=
  sorry

/-- A factorization between monomorphic field-valued points is an isomorphism of
source spectra. -/
theorem Factorization.isIso_schemeHom_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} [Mono p.hom] [Mono q.hom]
    (φ : p.Factorization q) : IsIso φ.schemeHom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint
