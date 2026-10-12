/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents

@[expose] public section

/-!
# Minimal primes of scheme stalks

This leaf records the finiteness of the minimal primes of local rings on a
scheme with finitely many irreducible components on quasi-compact opens.
-/

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The local ring at any point has finitely many minimal primes when every
quasi-compact open has finitely many irreducible components. -/
theorem stalk_finite_minimalPrimes (X : Scheme.{u})
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (x : X) :
    (minimalPrimes (X.presheaf.stalk x)).Finite := sorry

end AlgebraicGeometry.Scheme
