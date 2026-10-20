module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.SplitConic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.MinimalModel
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SplitConic
open scoped AlgebraicGeometry

noncomputable section

universe u

section Construction

variable (R : Type u) [CommRing R] (π : R)

/- The conic is the projective spectrum of its explicitly graded coordinate quotient. -/
#check (AlgebraicGeometry.SplitConic.model R π : Scheme)

/- The quotient-induced inclusion realizes the conic as a closed subscheme of the plane. -/
#check (AlgebraicGeometry.projQuotientMap_isClosedImmersion
  (ProjectiveSpace.grading R 2) (equationIdeal R π) :
    IsClosedImmersion (planeInclusion R π))

/- The two graded maps are the coordinate substitutions specified by the conic equation. -/
#check (AlgebraicGeometry.SplitConic.projectionGradedHom R π :
  Bool → ProjectiveSpace.grading R 1 →+*ᵍ grading R π)

#check (AlgebraicGeometry.SplitConic.projectionRingHom_apply R π :
  ∀ (second : Bool) (i : Fin 2),
    projectionRingHom R π second (MvPolynomial.X i) =
      Ideal.Quotient.mk (equationIdeal R π).toIdeal
        (MvPolynomial.X (projectionCoordinates second i)))

/- The coordinate projections extend to total morphisms over the coefficient ring. -/
#check (AlgebraicGeometry.SplitConic.projection R π :
  Bool → (model R π ⟶ ProjectiveSpace.scheme R 1))

#check (AlgebraicGeometry.SplitConic.projection_restrict_primary R π :
  ∀ second : Bool,
    (projectionCover R π second).f (ULift.up false) ≫ projection R π second =
      partialProjection R π second)

#check (AlgebraicGeometry.SplitConic.projection_over R π :
  ∀ second : Bool,
    projection R π second ≫ ProjectiveSpace.toSpec R 1 = toSpec R π)

end Construction

section Degeneration

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) [Fact (Irreducible π)]

/- The special fibre is the scheme-theoretic union of its two explicit components. -/
#check (AlgebraicGeometry.SplitConic.specialFiber_eq_union R π :
  (toSpec R π).specialFiberIdeal =
    (componentInclusion R π false).ker ⊓ (componentInclusion R π true).ker)

/- Each component is a projective line over the residue field. -/
#check (AlgebraicGeometry.SplitConic.component_iso_projectiveLine R π :
  ∀ second : Bool,
    Nonempty (Over.mk (componentToResidueField R π second) ≅
      ProjectiveSpace.schemeOver
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) 1))

/- The components are exceptional curves of the first kind. -/
#check (AlgebraicGeometry.SplitConic.component_isExceptionalCurve R π :
  ∀ second : Bool, IsExceptionalCurveFirstKind ((componentInclusion R π second).ker))

/- Each projection contracts the opposite component to the specified closed point. -/
#check (AlgebraicGeometry.SplitConic.projection_isContraction R π :
  ∀ second : Bool,
    IsContraction ((componentInclusion R π (!second)).ker)
      (projection R π second) (projectionCenter R))

/- Each projection identifies the retained component with the target special fibre. -/
#check (AlgebraicGeometry.SplitConic.componentProjection_isIso R π :
  ∀ second : Bool, IsIso (componentProjection R π second))

/- Each projection identifies the generic fibre with that of the projective line. -/
#check (AlgebraicGeometry.SplitConic.genericFiberProjection_isIso R π :
  ∀ second : Bool, IsIso (genericFiberProjection R π second))

/- The common target is a minimal model over the discrete valuation ring. -/
#check (AlgebraicGeometry.ProjectiveLine.isMinimalModel R :
  Scheme.Hom.IsMinimalModel (ProjectiveSpace.toSpec R 1))

/- Example 55.10.3: the two marked contractions are not intertwined by any target
isomorphism, giving nonunique minimal models in genus zero. -/
@[stacks 0CA0] #check (AlgebraicGeometry.SplitConic.minimalModels_nonunique R π :
  ¬ ∃ e : ProjectiveSpace.scheme R 1 ≅ ProjectiveSpace.scheme R 1,
    projection R π false ≫ e.hom = projection R π true)

end Degeneration
