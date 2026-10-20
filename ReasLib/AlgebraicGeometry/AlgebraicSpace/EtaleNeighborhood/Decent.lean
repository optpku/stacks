module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField

/-!
# Elementary étale neighbourhoods of decent algebraic spaces

Every point of a decent algebraic space has an affine elementary étale
neighbourhood with a singleton fibre. Elementary neighbourhoods can be
characterized by isomorphisms of the canonical residue spectra.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood

/-- Every point of a decent algebraic space admits an affine elementary étale
neighbourhood whose selected point is the only point over the given point. -/
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
