module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine

/-!
# Étale sites of formal algebraic spaces

The small, spaces, and affine étale sites of a formal algebraic space are the
corresponding sites of its explicitly supplied algebraic-space reduction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

/-- The category of schemes étale over the reduction of a formal algebraic space. -/
abbrev smallEtaleSite {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :=
  AlgebraicSpace.smallEtaleSite R.space

/-- The small étale category is the chart category of the algebraic-space reduction. -/
theorem smallEtaleSite_def {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :
    smallEtaleSite R = AlgebraicSpace.smallEtaleSite R.space := rfl

/-- The small étale topology of the algebraic-space reduction. -/
abbrev smallEtaleTopology {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :
    GrothendieckTopology (smallEtaleSite R) :=
  AlgebraicSpace.smallEtaleTopology R.space

/-- The small étale topology is the topology of the algebraic-space reduction. -/
theorem smallEtaleTopology_def {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :
    smallEtaleTopology R = AlgebraicSpace.smallEtaleTopology R.space := rfl

/-- The category of algebraic spaces étale over the reduction of a formal algebraic space. -/
abbrev spacesEtaleSite {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :=
  AlgebraicSpace.spacesEtaleSite R.space

/-- The spaces-étale category is the étale slice over the algebraic-space reduction. -/
theorem spacesEtaleSite_def {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :
    spacesEtaleSite R = AlgebraicSpace.spacesEtaleSite R.space := rfl

/-- The spaces-étale topology of the algebraic-space reduction. -/
abbrev spacesEtaleTopology {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :
    GrothendieckTopology (spacesEtaleSite R) :=
  AlgebraicSpace.spacesEtaleTopology R.space

/-- The spaces-étale topology is the topology of the algebraic-space reduction. -/
theorem spacesEtaleTopology_def {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :
    spacesEtaleTopology R = AlgebraicSpace.spacesEtaleTopology R.space := rfl

/-- The category of affine schemes étale over the reduction of a formal algebraic space. -/
abbrev affineEtaleSite {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :=
  AlgebraicSpace.affineEtaleSite R.space

/-- The affine étale category is the affine chart category of the algebraic-space reduction. -/
theorem affineEtaleSite_def {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :
    affineEtaleSite R = AlgebraicSpace.affineEtaleSite R.space := rfl

/-- The affine étale topology of the algebraic-space reduction. -/
abbrev affineEtaleTopology {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :
    GrothendieckTopology (affineEtaleSite R) :=
  AlgebraicSpace.affineEtaleTopology R.space

/-- The affine étale topology is the topology of the algebraic-space reduction. -/
theorem affineEtaleTopology_def {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :
    affineEtaleTopology R = AlgebraicSpace.affineEtaleTopology R.space := rfl

end AlgebraicGeometry.FormalAlgebraicSpace.ReductionData
