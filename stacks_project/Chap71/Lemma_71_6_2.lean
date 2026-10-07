module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap71.Lemma_71_6_2_Comparison

/-!
# Characterizations of effective Cartier divisors on algebraic spaces

Lemma 71.6.2 records that a closed subspace is an effective Cartier divisor iff
some surjective étale scheme atlas pulls it back to an effective Cartier
divisor, iff every étale morphism from a scheme does, iff it is cut out étale
locally on affine schemes by a nonzerodivisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsEffectiveCartierDivisor

/-- Lemma 71.6.2: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `D` be a closed subspace of `X`. The following are equivalent:
`IsEffectiveCartierDivisor D.ι`; for some scheme `U` and surjective étale
`φ : ofOver U ⟶ X`, `IsEffectiveCartierDivisor (D.inverseImage φ).ι`; for every
scheme `U` and étale `φ : ofOver U ⟶ X`,
`IsEffectiveCartierDivisor (D.inverseImage φ).ι`; and for every
`x ∈ D.pointsSet` there is an étale pointed map from an affine scheme `U` with
`Points.mapOfOver φ u = x` and `D.inverseImage φ` equal to the closed subscheme
cut out by a nonzerodivisor `f ∈ nonZeroDivisors Γ(U.left, ⊤)` via
`principalι`. -/
@[stacks 083C]
theorem tfae {S : Scheme.{u}} {X : AlgebraicSpace S} (D : ClosedSubspace X) :
    List.TFAE
      [IsEffectiveCartierDivisor D.ι, existsSurjectiveEtaleScheme D,
        forallEtaleScheme D, existsAffineEtaleNonZeroDivisor D] :=
  sorry

/-- A closed subspace is an effective Cartier divisor iff some surjective étale
morphism from a scheme pulls it back to an effective Cartier divisor. -/
theorem iff_existsSurjectiveEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) :
    IsEffectiveCartierDivisor D.ι ↔ existsSurjectiveEtaleScheme D :=
  sorry

/-- A closed subspace is an effective Cartier divisor iff every étale morphism
from a scheme pulls it back to an effective Cartier divisor. -/
theorem iff_forallEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) :
    IsEffectiveCartierDivisor D.ι ↔ forallEtaleScheme D :=
  sorry

/-- A closed subspace is an effective Cartier divisor iff at every point of
`|D|` it is cut out on an affine étale chart by a nonzerodivisor. -/
theorem iff_existsAffineEtaleNonZeroDivisor {S : Scheme.{u}}
    {X : AlgebraicSpace S} (D : ClosedSubspace X) :
    IsEffectiveCartierDivisor D.ι ↔ existsAffineEtaleNonZeroDivisor D :=
  sorry

end IsEffectiveCartierDivisor

end AlgebraicGeometry.AlgebraicSpace
