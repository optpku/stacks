/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Etale.Neighborhood
public import ReasLib.RingTheory.MvPolynomial.Solution

@[expose] public section

/-!
# Exact approximation at a closed point

This leaf owns the reusable approximation datum in an etale neighborhood of
a local ring's closed point.  Existence under regularity hypotheses lives in
the separate `Existence` leaf.
-/

open IsLocalRing MvPolynomial

universe u v w x

namespace PrimeSpectrum.ArtinApproximation

/-- An exact approximation in an etale neighborhood of the closed point,
together with the comparison map selecting the relevant branch. -/
@[stacks 07QZ "bundled closed-point etale approximation"]
structure AtClosedPoint
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)]
    {sigma : Type w} {iota : Type x} (f : iota → MvPolynomial sigma R)
    (aHat : sigma → AdicCompletion (maximalIdeal R) R) (N : ℕ) where
  /-- The etale neighborhood containing the exact solution. -/
  neighborhood : EtaleNeighborhood.{u, v} (closedPoint R)
  /-- The comparison map from the neighborhood to the completion. -/
  comparison : neighborhood.carrier →ₐ[R]
    AdicCompletion (maximalIdeal R) R
  /-- The comparison map selects the bundled point of the neighborhood. -/
  branch : PrimeSpectrum.comap comparison.toRingHom
      (closedPoint (AdicCompletion (maximalIdeal R) R)) =
    neighborhood.point
  /-- The exact solution and its prescribed congruence in the completion. -/
  approximation : SolutionApproximation f aHat comparison
    (Ideal.map comparison.toRingHom (neighborhood.point.asIdeal ^ N))

namespace AtClosedPoint

/-- Bundle a closed-point etale neighborhood, its comparison map, selected
branch, and exact approximate solution. -/
def of
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)]
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → AdicCompletion (maximalIdeal R) R} {N : ℕ}
    (U : EtaleNeighborhood.{u, v} (closedPoint R))
    (phi : U.carrier →ₐ[R] AdicCompletion (maximalIdeal R) R)
    (hbranch : PrimeSpectrum.comap phi.toRingHom
        (closedPoint (AdicCompletion (maximalIdeal R) R)) = U.point)
    (approximation : SolutionApproximation f aHat phi
      (Ideal.map phi.toRingHom (U.point.asIdeal ^ N))) :
    AtClosedPoint (R := R) f aHat N where
  neighborhood := U
  comparison := phi
  branch := hbranch
  approximation := approximation

/-- The neighborhood of a constructed closed-point approximation is the
supplied etale neighborhood. -/
@[simp]
theorem neighborhood_of
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)]
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → AdicCompletion (maximalIdeal R) R} {N : ℕ}
    (U : EtaleNeighborhood.{u, v} (closedPoint R))
    (phi : U.carrier →ₐ[R] AdicCompletion (maximalIdeal R) R)
    (hbranch : PrimeSpectrum.comap phi.toRingHom
        (closedPoint (AdicCompletion (maximalIdeal R) R)) = U.point)
    (approximation : SolutionApproximation f aHat phi
      (Ideal.map phi.toRingHom (U.point.asIdeal ^ N))) :
    (of U phi hbranch approximation).neighborhood = U := sorry

/-- The comparison map of a constructed closed-point approximation is the
supplied comparison map. -/
@[simp]
theorem comparison_of
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)]
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → AdicCompletion (maximalIdeal R) R} {N : ℕ}
    (U : EtaleNeighborhood.{u, v} (closedPoint R))
    (phi : U.carrier →ₐ[R] AdicCompletion (maximalIdeal R) R)
    (hbranch : PrimeSpectrum.comap phi.toRingHom
        (closedPoint (AdicCompletion (maximalIdeal R) R)) = U.point)
    (approximation : SolutionApproximation f aHat phi
      (Ideal.map phi.toRingHom (U.point.asIdeal ^ N))) :
    (of U phi hbranch approximation).comparison = phi := sorry

/-- The approximation carried by the closed-point constructor is the
supplied exact approximation. -/
@[simp]
theorem approximation_of
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)]
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → AdicCompletion (maximalIdeal R) R} {N : ℕ}
    (U : EtaleNeighborhood.{u, v} (closedPoint R))
    (phi : U.carrier →ₐ[R] AdicCompletion (maximalIdeal R) R)
    (hbranch : PrimeSpectrum.comap phi.toRingHom
        (closedPoint (AdicCompletion (maximalIdeal R) R)) = U.point)
    (approximation : SolutionApproximation f aHat phi
      (Ideal.map phi.toRingHom (U.point.asIdeal ^ N))) :
    (of U phi hbranch approximation).approximation = approximation := sorry

/-- The selected point of a closed-point approximation lies over the closed
point of the base ring. -/
@[stacks 07QZ "selected point of a closed-point approximation"]
theorem comap_point
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)]
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → AdicCompletion (maximalIdeal R) R} {N : ℕ}
    (P : AtClosedPoint.{u, v, w, x} f aHat N) :
    PrimeSpectrum.comap (algebraMap R P.neighborhood.carrier)
      P.neighborhood.point = closedPoint R := sorry

/-- The selected point of a closed-point approximation has the same residue
field as the closed point of the base ring. -/
@[stacks 07QZ "residue field of a closed-point approximation"]
theorem residueFieldBijectiveAt
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)]
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → AdicCompletion (maximalIdeal R) R} {N : ℕ}
    (P : AtClosedPoint.{u, v, w, x} f aHat N) :
    RingHom.ResidueField.IsBijectiveAt
      (algebraMap R P.neighborhood.carrier) P.neighborhood.point := sorry

/-- The chosen tuple of a closed-point approximation has the bundled exact
approximation property. -/
@[stacks 07QZ "closed-point exact approximation"]
theorem isApproximation
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)]
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → AdicCompletion (maximalIdeal R) R} {N : ℕ}
    (P : AtClosedPoint.{u, v, w, x} f aHat N) :
    IsApproximation f aHat P.comparison
      (Ideal.map P.comparison.toRingHom
        (P.neighborhood.point.asIdeal ^ N)) P.approximation.solution := sorry

/-- The chosen tuple of a closed-point approximation is an exact solution
of the original polynomial system. -/
@[stacks 07QZ "closed-point exact solution"]
theorem isSolution
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)]
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → AdicCompletion (maximalIdeal R) R} {N : ℕ}
    (P : AtClosedPoint.{u, v, w, x} f aHat N) :
    IsSolution f P.approximation.solution := sorry

/-- Every coordinate of the chosen exact solution has the prescribed
closed-point congruence. -/
@[stacks 07QZ "closed-point solution congruence"]
theorem modEq
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)]
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → AdicCompletion (maximalIdeal R) R} {N : ℕ}
    (P : AtClosedPoint.{u, v, w, x} f aHat N) (i : sigma) :
    aHat i ≡ P.comparison (P.approximation.solution i)
      [SMOD Ideal.map P.comparison.toRingHom
        (P.neighborhood.point.asIdeal ^ N)] := sorry

/-- The etale-neighborhood, selected-branch, and exact-approximation
properties carried by a closed-point approximation. -/
@[stacks 07QZ "closed-point etale approximation specification"]
theorem spec
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)]
    {sigma : Type w} {iota : Type x} {f : iota → MvPolynomial sigma R}
    {aHat : sigma → AdicCompletion (maximalIdeal R) R} {N : ℕ}
    (P : AtClosedPoint.{u, v, w, x} f aHat N) :
    (Algebra.Etale R P.neighborhood.carrier ∧
      PrimeSpectrum.comap (algebraMap R P.neighborhood.carrier)
          P.neighborhood.point = closedPoint R ∧
      RingHom.ResidueField.IsBijectiveAt
        (algebraMap R P.neighborhood.carrier) P.neighborhood.point) ∧
      PrimeSpectrum.comap P.comparison.toRingHom
        (closedPoint (AdicCompletion (maximalIdeal R) R)) =
        P.neighborhood.point ∧
      IsApproximation f aHat P.comparison
        (Ideal.map P.comparison.toRingHom
          (P.neighborhood.point.asIdeal ^ N)) P.approximation.solution := sorry

end AtClosedPoint

end PrimeSpectrum.ArtinApproximation
