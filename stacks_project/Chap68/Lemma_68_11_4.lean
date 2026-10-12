/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap68.Definition_68_11_2_ResidueField
public import stacks_project.Chap68.Definition_68_11_5_Neighborhood

/-!
# Affine elementary étale neighbourhoods of points of decent algebraic spaces

A decent algebraic space admits, at every point, an étale neighbourhood from an
affine scheme whose selected point is the unique point over the given point and
whose residue-field homomorphism is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood

/-- Lemma 68.11.4: Let `S` be a scheme. Let `X` be a decent algebraic space over
`S`. For every point `x` of `|X|` there exists an étale morphism
`(U, u) ⟶ (X, x)` where `U` is an affine scheme, `u` is the only point of `U`
lying over `x`, and the induced homomorphism `κ(x) ⟶ κ(u)` is an isomorphism. -/
@[stacks 0BBP]
theorem exists_affine_elementary {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) :
    ∃ U : EtaleNeighborhood X x,
      IsAffine U.scheme ∧ Points.mapOfOver U.hom ⁻¹' {x} = {U.point} ∧
        U.IsElementary :=
  sorry

/-- A decent algebraic space has a nonempty category of elementary étale
neighbourhoods at every point. -/
theorem nonempty_elementary {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : Nonempty (Elementary X x) :=
  sorry

/-- An étale neighbourhood of a point of a decent algebraic space is elementary
if and only if a factorization of `Spec(κ(u)) ⟶ X` through `Spec(κ(x)) ⟶ X`
is an isomorphism of source spectra, equivalently if `κ(x) ⟶ κ(u)` is an
isomorphism. -/
theorem isElementary_iff_isIso_residueFactor {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} (U : EtaleNeighborhood X x)
    (φ : FieldValuedPoint.Factorization (residuePoint U)
      (FieldValuedPoint.residuePoint x)) :
    U.IsElementary ↔ IsIso φ.schemeHom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
