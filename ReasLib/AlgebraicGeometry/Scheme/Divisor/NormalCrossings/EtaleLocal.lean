/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Noetherian

/-!
# Étale-local normal crossings divisors

This module defines normal crossings divisors by strict normal crossings on pointed étale
neighbourhoods of their support points.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- An effective Cartier divisor on a locally Noetherian scheme has normal crossings when,
after passing to a pointed étale neighbourhood of each point of its support, its pullback is a
strict normal crossings divisor. -/
class IsNormalCrossingsDivisor {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) : Prop extends IsEffectiveCartierDivisor D.subschemeι where
  locallyStrict :
    ∀ p : X, p ∈ D.support →
      ∃ U : Scheme.EtaleNeighborhood X p,
        IsStrictNormalCrossingsDivisor
          (D.comap U.toEtale.hom : U.toEtale.left.IdealSheafData)

namespace IsNormalCrossingsDivisor

/-- A normal crossings divisor is canonically an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisor {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) [hD : IsNormalCrossingsDivisor D] :
    IsEffectiveCartierDivisor D.subschemeι := hD.toIsEffectiveCartierDivisor

/-- At every point of a normal crossings divisor there is a pointed étale neighbourhood on
which its pullback is a strict normal crossings divisor. -/
theorem exists_etaleNeighborhood {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) [hD : IsNormalCrossingsDivisor D]
    (p : X) (hp : p ∈ D.support) :
    ∃ U : Scheme.EtaleNeighborhood X p,
      IsStrictNormalCrossingsDivisor
        (D.comap U.toEtale.hom : U.toEtale.left.IdealSheafData) := sorry

end IsNormalCrossingsDivisor

/-- A divisor has normal crossings exactly when it is effective Cartier and becomes strict
normal crossings on a pointed étale neighbourhood of every support point. -/
theorem isNormalCrossingsDivisor_iff {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) :
    IsNormalCrossingsDivisor D ↔
      IsEffectiveCartierDivisor D.subschemeι ∧
        ∀ p : X, p ∈ D.support →
          ∃ U : Scheme.EtaleNeighborhood X p,
            IsStrictNormalCrossingsDivisor
              (D.comap U.toEtale.hom : U.toEtale.left.IdealSheafData) := sorry

namespace IsStrictNormalCrossingsDivisor

/-- A strict normal crossings divisor is canonically a normal crossings divisor. -/
instance instIsNormalCrossingsDivisor {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) [IsStrictNormalCrossingsDivisor D] :
    IsNormalCrossingsDivisor D := sorry

end IsStrictNormalCrossingsDivisor

end AlgebraicGeometry
