module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.NeighborhoodComparison
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Regular.Defs

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.finiteEtaleNeighborhoodRestriction

/-- Full faithfulness of restriction from finite étale neighborhoods under finite local
cohomology of a principal quotient. -/
theorem fullyFaithful_of_finiteLocalCohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    [IsAdicComplete (Ideal.span ({(f : A)} : Set A)) A]
    (h_regular : IsRegular (f : A))
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 1).obj
        (ModuleCat.of A (A ⧸ Ideal.span ({(f : A)} : Set A))))] :
    let S := AffineAlgebraizationSetup.ofPrincipal (maximalIdeal A) (f : A) f.property
    let I := AffineAlgebraizationSetup.idealOnOpen S
    ∀ (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)),
      Nonempty (finiteEtaleNeighborhoodRestriction I t).FullyFaithful := sorry

end AlgebraicGeometry.Scheme.finiteEtaleNeighborhoodRestriction
