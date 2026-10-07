module

public import stacks_project.Chap68.Definition_68_11_2_ResidueField

/-!
# Identifying residue fields along a morphism of decent algebraic spaces

A morphism of decent algebraic spaces induces a homomorphism of residue fields at a
point, recorded as a factorization of the composite `Spec(κ(x)) ⟶ Y` through
`Spec(κ(f(x))) ⟶ Y`. That homomorphism is an isomorphism if and only if the
composite is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open FieldValuedPoint

/-- For monomorphic field-valued points `p` of `X` and `q` of `Y`, a factorization of
`p.map f` through `q` is an isomorphism of source spectra if and only if the
composite `p.hom ≫ f` is a monomorphism. -/
theorem isIso_factorization_iff_mono_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {p : FieldValuedPoint X} {q : FieldValuedPoint Y} [Mono p.hom] [Mono q.hom]
    (f : X ⟶ Y) (φ : Factorization (p.map f) q) :
    IsIso φ.schemeHom ↔ Mono (p.hom ≫ f) :=
  sorry

/-- The composite `Spec(κ(x)) ⟶ Y` factors through `Spec(κ(Points.map f x)) ⟶ Y`. -/
theorem exists_residuePointFactor {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    Nonempty (Factorization ((residuePoint x).map f)
      (residuePoint (Points.map f x))) :=
  sorry

/-- A factorization of `Spec(κ(x)) ⟶ Y` through `Spec(κ(Points.map f x)) ⟶ Y` is
unique. -/
theorem subsingleton_residuePointFactor {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    Subsingleton (Factorization ((residuePoint x).map f)
      (residuePoint (Points.map f x))) :=
  sorry

/-- Lemma 68.11.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of decent
algebraic spaces over `S`. Let `x` be a point of `X` with image `y = Points.map f x`.
The following are equivalent: `f` induces an isomorphism `κ(y) ⟶ κ(x)`, and the
induced morphism `Spec(κ(x)) ⟶ Y` is a monomorphism.

The induced field homomorphism is the source-spectrum map of a factorization of
`(residuePoint x).map f` through `residuePoint (Points.map f x)`. -/
@[stacks 0EMX]
theorem identifiesResidueFields_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X)
    (φ : Factorization ((residuePoint x).map f) (residuePoint (Points.map f x))) :
    IsIso φ.schemeHom ↔ Mono (X.fromSpecResidueField x ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
