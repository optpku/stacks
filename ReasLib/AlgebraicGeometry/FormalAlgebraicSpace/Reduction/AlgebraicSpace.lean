module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening

/-!
# Reductions of algebraic spaces as formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- The functor of points of an algebraic space is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_functorOfPoints (X : AlgebraicSpace S) :
    IsFormalAlgebraicSpace X.functorOfPoints :=
  sorry

/-- The canonical reduction of an algebraic space is reduced. -/
theorem isReduced_algebraicSpaceReduction (X : AlgebraicSpace S) :
    AlgebraicSpace.existsSurjectiveEtale
      (IsReduced : ObjectProperty Scheme.{u}) (AlgebraicSpace.reduction X) :=
  sorry

/-- Every Yoneda pullback of the canonical reduction inclusion is a thickening. -/
theorem isThickening_algebraicSpaceReductionι (X : AlgebraicSpace S)
    {U : Over S} (ξ : yoneda.obj U ⟶ X.functorOfPoints) :
    AlgebraicSpace.IsThickening
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom
        (AlgebraicSpace.representableByAlgebraicSpaces.of_hom
          (AlgebraicSpace.reductionι X)) ξ) :=
  sorry

/-- A map from a reduced algebraic space factors uniquely through the canonical reduction. -/
theorem liftUnique_algebraicSpaceReduction (X : AlgebraicSpace S)
    {U : AlgebraicSpace S}
    (hU : AlgebraicSpace.existsSurjectiveEtale
      (IsReduced : ObjectProperty Scheme.{u}) U)
    (g : U.functorOfPoints ⟶ X.functorOfPoints) :
    ∃! h : U.functorOfPoints ⟶ (AlgebraicSpace.reduction X).functorOfPoints,
      h ≫ AlgebraicSpace.reductionι X = g :=
  sorry

/-- The canonical reduction of an algebraic space supplies explicit reduction data. -/
def ReductionData.ofAlgebraicSpace (X : AlgebraicSpace S) :
    ReductionData X.functorOfPoints where
  space := AlgebraicSpace.reduction X
  ι := AlgebraicSpace.reductionι X
  isReduced := isReduced_algebraicSpaceReduction X
  representable := AlgebraicSpace.representableByAlgebraicSpaces.of_hom
    (AlgebraicSpace.reductionι X)
  isThickening := fun {_} ξ ↦
    ⟨(isThickening_algebraicSpaceReductionι X ξ).toIsClosedImmersion,
      (isThickening_algebraicSpaceReductionι X ξ).toSurjective.map_surjective⟩
  liftUnique := liftUnique_algebraicSpaceReduction X

end AlgebraicGeometry.FormalAlgebraicSpace
