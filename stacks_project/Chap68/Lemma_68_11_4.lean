module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap68.Definition_68_11_2_ResidueField
public import stacks_project.Chap68.Definition_68_11_5_Neighborhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Decent
import StacksCheckRecall

/-!
# Affine elementary étale neighbourhoods of points of decent algebraic spaces

A decent algebraic space admits, at every point, an étale neighbourhood from an
affine scheme whose selected point is the unique point over the given point and
whose residue-field homomorphism is an isomorphism.

Elementary means that the residue-spectrum morphism `Spec(κ(u)) ⟶ X` is a
monomorphism. For a decent target this is equivalent to the induced residue-field
homomorphism being an isomorphism, as expressed by
`isElementary_iff_isIso_residueFactor`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood

/- Lemma 68.11.4: Let `S` be a scheme. Let `X` be a decent algebraic space over
`S`. For every point `x` of `|X|` there exists an étale morphism
`(U, u) ⟶ (X, x)` where `U` is an affine scheme, `u` is the only point of `U`
lying over `x`, and the induced homomorphism `κ(x) ⟶ κ(u)` is an isomorphism. -/
@[stacks 0BBP] #check
  (AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.exists_affine_elementary :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X),
    ∃ U : EtaleNeighborhood X x,
      IsAffine U.scheme ∧ Points.mapOfOver U.hom ⁻¹' {x} = {U.point} ∧
        U.IsElementary)

/- A decent algebraic space has a nonempty category of elementary étale
neighbourhoods at every point. -/
#check (AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.nonempty_elementary :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X),
    Nonempty (Elementary X x))

/- An étale neighbourhood of a point of a decent algebraic space is elementary
if and only if a factorization of `Spec(κ(u)) ⟶ X` through `Spec(κ(x)) ⟶ X`
is an isomorphism of source spectra, equivalently if `κ(x) ⟶ κ(u)` is an
isomorphism. -/
#check (AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.isElementary_iff_isIso_residueFactor :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} (U : EtaleNeighborhood X x)
    (φ : FieldValuedPoint.Factorization (residuePoint U)
      (FieldValuedPoint.residuePoint x)),
    U.IsElementary ↔ IsIso φ.schemeHom)

end AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
