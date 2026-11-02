/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime.Congruence
public import ReasLib.RingTheory.Etale.Neighborhood.Completion
public import ReasLib.RingTheory.MvPolynomial.Solution

@[expose] public section

/-!
# Exact approximation at a prime

This leaf owns exact approximation in an etale neighborhood after
transporting a formal solution to the completed local ring at the selected
point.  Existence under regularity hypotheses is kept in a separate leaf.
-/

open MvPolynomial

universe u v w x

namespace PrimeSpectrum.ArtinApproximation

/-- An exact approximation in an etale neighborhood of a prime, after
transporting the formal solution to the completed local ring at the selected
point. -/
@[stacks 0CAR "bundled primewise etale approximation"]
structure AtPrime
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    {sigma : Type w} {iota : Type x} (f : iota → MvPolynomial sigma R)
    (aHat : sigma → CompletedLocalRing p) (N : ℕ) where
  /-- The etale neighborhood containing the exact solution. -/
  neighborhood : EtaleNeighborhood.{u, v} p
  /-- The transported formal tuple and its exact approximation. -/
  approximation : SolutionApproximation f
    (fun i ↦ neighborhood.completedLocalMap (aHat i))
    neighborhood.toCompletedLocalRing
    (completedMaximalIdealPow neighborhood.point N)

namespace AtPrime

/-- Bundle an etale neighborhood with an exact approximation of the
transported formal solution. -/
def of
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → CompletedLocalRing p} {N : ℕ}
    (U : EtaleNeighborhood.{u, v} p)
    (approximation : SolutionApproximation f
      (fun i ↦ U.completedLocalMap (aHat i)) U.toCompletedLocalRing
      (completedMaximalIdealPow U.point N)) :
    AtPrime (R := R) p f aHat N where
  neighborhood := U
  approximation := approximation

/-- The neighborhood of a constructed primewise approximation is the
supplied etale neighborhood. -/
@[simp]
theorem neighborhood_of
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → CompletedLocalRing p} {N : ℕ}
    (U : EtaleNeighborhood.{u, v} p)
    (approximation : SolutionApproximation f
      (fun i ↦ U.completedLocalMap (aHat i)) U.toCompletedLocalRing
      (completedMaximalIdealPow U.point N)) :
    (of U approximation).neighborhood = U := rfl

/-- The approximation carried by the primewise constructor is the supplied
exact approximation. -/
@[simp]
theorem approximation_of
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → CompletedLocalRing p} {N : ℕ}
    (U : EtaleNeighborhood.{u, v} p)
    (approximation : SolutionApproximation f
      (fun i ↦ U.completedLocalMap (aHat i)) U.toCompletedLocalRing
      (completedMaximalIdealPow U.point N)) :
    (of U approximation).approximation = approximation := rfl

/-- The selected point of a primewise approximation lies over the original
prime. -/
@[stacks 0CAR "selected point of a primewise approximation"]
theorem comap_point
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → CompletedLocalRing p} {N : ℕ}
    (P : AtPrime.{u, v, w, x} p f aHat N) :
    PrimeSpectrum.comap (algebraMap R P.neighborhood.carrier)
      P.neighborhood.point = p := by
  apply PrimeSpectrum.ext
  exact P.neighborhood.over.symm

/-- The selected point of a primewise approximation has the same residue
field as the original prime. -/
@[stacks 0CAR "residue field of a primewise approximation"]
theorem residueFieldBijectiveAt
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → CompletedLocalRing p} {N : ℕ}
    (P : AtPrime.{u, v, w, x} p f aHat N) :
    RingHom.ResidueField.IsBijectiveAt
      (algebraMap R P.neighborhood.carrier) P.neighborhood.point := by
  rcases p with ⟨p, hp⟩
  rcases P with ⟨⟨S, q, hq, hres⟩, A⟩
  cases hq
  exact hres

/-- The chosen tuple of a primewise approximation has the bundled exact
approximation property. -/
@[stacks 0CAR "primewise exact approximation"]
theorem isApproximation
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → CompletedLocalRing p} {N : ℕ}
    (P : AtPrime.{u, v, w, x} p f aHat N) :
    IsApproximation f
      (fun i ↦ P.neighborhood.completedLocalMap (aHat i))
      P.neighborhood.toCompletedLocalRing
      (completedMaximalIdealPow P.neighborhood.point N)
      P.approximation.solution := P.approximation.isApproximation

/-- The chosen tuple of a primewise approximation is an exact solution of
the original polynomial system. -/
@[stacks 0CAR "primewise exact solution"]
theorem isSolution
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → CompletedLocalRing p} {N : ℕ}
    (P : AtPrime.{u, v, w, x} p f aHat N) :
    IsSolution f P.approximation.solution := P.approximation.isSolution

/-- Every coordinate of the chosen exact solution has the prescribed
primewise congruence. -/
@[stacks 0CAR "primewise solution congruence"]
theorem modEq
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → CompletedLocalRing p} {N : ℕ}
    (P : AtPrime.{u, v, w, x} p f aHat N) (i : sigma) :
    P.neighborhood.completedLocalMap (aHat i) ≡
      P.neighborhood.toCompletedLocalRing (P.approximation.solution i)
      [SMOD completedMaximalIdealPow P.neighborhood.point N] := P.approximation.modEq i

/-- The etale-neighborhood and exact-approximation properties carried by a
primewise approximation. -/
@[stacks 0CAR "primewise etale approximation specification"]
theorem spec
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → CompletedLocalRing p} {N : ℕ}
    (P : AtPrime.{u, v, w, x} p f aHat N) :
    (Algebra.Etale R P.neighborhood.carrier ∧
      PrimeSpectrum.comap (algebraMap R P.neighborhood.carrier)
          P.neighborhood.point = p ∧
      RingHom.ResidueField.IsBijectiveAt
        (algebraMap R P.neighborhood.carrier) P.neighborhood.point) ∧
      IsApproximation f
        (fun i ↦ P.neighborhood.completedLocalMap (aHat i))
        P.neighborhood.toCompletedLocalRing
        (completedMaximalIdealPow P.neighborhood.point N)
        P.approximation.solution := by
  exact ⟨⟨inferInstance, P.comap_point, P.residueFieldBijectiveAt⟩, P.isApproximation⟩

end AtPrime

end PrimeSpectrum.ArtinApproximation
