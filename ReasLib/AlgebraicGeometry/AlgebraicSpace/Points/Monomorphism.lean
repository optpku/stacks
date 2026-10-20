module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A monomorphism of algebraic spaces over a scheme induces an injective map on points. -/
@[stacks 06RV]
theorem Points.map_injective_of_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Mono f] : Function.Injective (Points.map f) := sorry

namespace FieldValuedPoint

/-- A field-valued point representing the same point as a monomorphic field-valued point
factors uniquely through it. -/
theorem unique_factorization_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} (hq : Mono q.hom) (h : Points.mk p = Points.mk q) :
    Nonempty (p.Factorization q) ∧ Subsingleton (p.Factorization q) :=
  sorry

/-- A monomorphic field-valued point factors uniquely through any monomorphic field-valued
point representing the same point of the algebraic space. -/
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

/-- Monomorphic field-valued points representing the same point of an algebraic space
are uniquely isomorphic over that algebraic space. -/
theorem unique_iso_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} [Mono p.hom] [Mono q.hom]
    (h : Points.mk p = Points.mk q) :
    Nonempty (p ≅ q) ∧ Subsingleton (p ≅ q) :=
  sorry

end FieldValuedPoint

/-- For monomorphic field-valued points `p` of `X` and `q` of `Y`, a factorization of
`p.map f` through `q` is an isomorphism of source spectra if and only if the
composite `p.hom ≫ f` is a monomorphism. -/
theorem isIso_factorization_iff_mono_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {p : FieldValuedPoint X} {q : FieldValuedPoint Y} [Mono p.hom] [Mono q.hom]
    (f : X ⟶ Y) (φ : FieldValuedPoint.Factorization (p.map f) q) :
    IsIso φ.schemeHom ↔ Mono (p.hom ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
