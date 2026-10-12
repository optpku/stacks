/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Basic
public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization

@[expose] public section

/-!
# Normalization stalks with finite irreducible components

This leaf compares the normalization pushforward stalk with integral closures
in the total quotient ring of the reduced stalk and in the product of the
residue fields of its minimal primes.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Normalization.Stalk

variable (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
variable (x : X)

/-- The integral closure of a local ring in the total quotient ring of its
reduction is ring-equivalent, compatibly with the local-ring maps, to its
integral closure in the product of its minimal-prime residue fields. -/
theorem reducedIntegralClosure_exists_ringEquiv_piResidueFields :
    ∃ e : reducedIntegralClosure X x ≃+*
        integralClosure (X.presheaf.stalk x)
          ((q : minimalPrimes (X.presheaf.stalk x)) → q.1.ResidueField),
      e.toRingHom.comp
          (algebraMap (X.presheaf.stalk x) (reducedIntegralClosure X x)) =
        algebraMap (X.presheaf.stalk x)
          (integralClosure (X.presheaf.stalk x)
            ((q : minimalPrimes (X.presheaf.stalk x)) → q.1.ResidueField)) := sorry

/-- The normalization pushforward stalk is ring-equivalent, compatibly with
the maps from the source stalk, to the integral closure in the total quotient
ring of the reduced source stalk. -/
theorem pushforward_exists_ringEquiv_reducedIntegralClosure :
    ∃ e : pushforward X x ≃+* reducedIntegralClosure X x,
      e.toRingHom.comp (pushforwardMap X x) =
        algebraMap (X.presheaf.stalk x) (reducedIntegralClosure X x) := sorry

end AlgebraicGeometry.Scheme.Normalization.Stalk
