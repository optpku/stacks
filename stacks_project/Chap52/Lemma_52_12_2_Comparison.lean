module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.GlobalSections

@[expose] public section

open CategoryTheory.Limits

universe u

/- The canonical comparison from neighborhood sections to global ideal-power quotient sections. -/
#check (AlgebraicGeometry.AffineAlgebraizationSetup.globalNeighborhoodComparison :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AlgebraicGeometry.AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules),
    colimit (AlgebraicGeometry.AffineAlgebraizationSetup.neighborhoodSectionsDiagram S M) ⟶
      limit (AlgebraicGeometry.Scheme.CoherentCompletion.positiveSectionsSystem
        (AlgebraicGeometry.AffineAlgebraizationSetup.idealOnOpen S) M))
