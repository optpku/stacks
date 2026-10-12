/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Graded
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Clifford
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.RiemannRoch
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Dimension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme Scheme.Hom Scheme.Modules
open Scheme.DerivedQCoh
open ProperDualizingComplex

universe u v w

/- Exercise 111.56.2 (Results) (1): Hilbert polynomials of graded modules. -/
@[stacks 09TX] #check
  (CategoryTheory.ModuleCat.K0.gradedPieceClass_of_isNoetherian_isNumericalPolynomial :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
      (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule R M)
      [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
      [IsNoetherianRing S] [Module.Finite S M],
      Ideal.span (𝒜 1 : Set S) = (HomogeneousIdeal.irrelevant 𝒜).toIdeal →
        IsNumericalPolynomial
          (ModuleCat.K0.gradedPieceClass_of_isNoetherian 𝒜 ℳ))

/- Exercise 111.56.2 (Results) (2): the Krull dimension of a Noetherian local ring `R`
equals the Krull dimension of the associated graded ring `⨁ n, m^n / m^{n+1}` of its
maximal ideal. -/
@[stacks 09TX] #check
  (IsLocalRing.ringKrullDim_eq_associatedGraded :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      ringKrullDim R =
        ringKrullDim (Ideal.AssociatedGraded.ring (IsLocalRing.maximalIdeal R)))

/- Exercise 111.56.2 (Results) (3): Riemann–Roch. -/
@[stacks 09TX] #check
  (AlgebraicGeometry.SchemeOverField.riemannRoch :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [Scheme.Gorenstein X.left] [EquidimensionalSpace X.left]
      [h_dimension : Fact (topologicalKrullDim X.left = 1)]
      (E : X.left.Modules) (n : ℕ) [E.IsFiniteLocallyFreeOfRank n],
      (eulerCharacteristic X.hom E : ℚ) =
        (curveDegree X.hom h_dimension.out.le E n : ℚ) -
          (n : ℚ) *
            (curveDegreeOfInvertible X.hom h_dimension.out.le
              (curveDualizingModule X.hom) : ℚ) / 2)

/- Exercise 111.56.2 (Results) (4): Clifford's theorem for a special invertible module
on a smooth projective geometrically irreducible curve: twice the zeroth cohomology
finrank is at most the degree plus two. -/
@[stacks 09TX] #check
  (AlgebraicGeometry.SchemeOverField.clifford :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
      (L : X.left.Modules) [Invertible L]
      (h0 : 0 < cohomologyFinrank X.hom L 0)
      (h1 : 0 < cohomologyFinrank X.hom L 1),
      2 * (cohomologyFinrank X.hom L 0 : ℤ) ≤
        curveDegreeOfInvertible X.hom
          (topologicalKrullDim_eq_one X).le L + 2)

/- Exercise 111.56.2 (Results) (5): Chevalley's theorem. -/
@[stacks 09TX] #check
  (AlgebraicGeometry.Scheme.Hom.chevalley :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [LocallyOfFinitePresentation f] [QuasiCompact f] {s : Set X},
      Topology.IsLocallyConstructible s → Topology.IsLocallyConstructible (f '' s))
