module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleSite.Basic
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap87.Definition_87_25_1_Surjective

/-!
# Small étale sites of a formal algebraic space

The three small étale sites of a formal algebraic space `X` are the
corresponding étale sites of its algebraic-space reduction `reduction X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The underlying category of the small étale site of a formal algebraic space:
schemes étale over its algebraic-space reduction. -/
abbrev smallEtaleSite {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [R : Reduction X] :=
  ReductionData.smallEtaleSite R.toReductionData

/-- The small étale site of a formal algebraic space is the small étale site of
its reduction. -/
theorem smallEtaleSite_def {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X] :
    smallEtaleSite X = AlgebraicSpace.smallEtaleSite (reduction X) := rfl

/-- The small étale topology of a formal algebraic space is the small étale
topology of its algebraic-space reduction. -/
abbrev smallEtaleTopology {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [R : Reduction X] :
    GrothendieckTopology (smallEtaleSite X) :=
  ReductionData.smallEtaleTopology R.toReductionData

/-- The small étale topology of a formal algebraic space is the small étale
topology of its reduction. -/
theorem smallEtaleTopology_def {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X] :
    smallEtaleTopology X = AlgebraicSpace.smallEtaleTopology (reduction X) :=
  rfl

/-- The underlying category of the étale site of algebraic spaces over a formal
algebraic space: algebraic spaces étale over its reduction. -/
abbrev spacesEtaleSite {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [R : Reduction X] :=
  ReductionData.spacesEtaleSite R.toReductionData

/-- The étale site of algebraic spaces over a formal algebraic space is the
étale site of algebraic spaces over its reduction. -/
theorem spacesEtaleSite_def {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X] :
    spacesEtaleSite X = AlgebraicSpace.spacesEtaleSite (reduction X) := rfl

/-- The étale topology of algebraic spaces over a formal algebraic space is the
étale topology of algebraic spaces over its reduction. -/
abbrev spacesEtaleTopology {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [R : Reduction X] :
    GrothendieckTopology (spacesEtaleSite X) :=
  ReductionData.spacesEtaleTopology R.toReductionData

/-- The étale topology of algebraic spaces over a formal algebraic space is the
étale topology of algebraic spaces over its reduction. -/
theorem spacesEtaleTopology_def {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X] :
    spacesEtaleTopology X = AlgebraicSpace.spacesEtaleTopology (reduction X) :=
  rfl

/-- The underlying category of the affine étale site of a formal algebraic
space: affine schemes étale over its reduction. -/
abbrev affineEtaleSite {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [R : Reduction X] :=
  ReductionData.affineEtaleSite R.toReductionData

/-- The affine étale site of a formal algebraic space is the affine étale site
of its reduction. -/
theorem affineEtaleSite_def {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X] :
    affineEtaleSite X = AlgebraicSpace.affineEtaleSite (reduction X) := rfl

/-- The affine étale topology of a formal algebraic space is the affine étale
topology of its algebraic-space reduction. -/
abbrev affineEtaleTopology {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [R : Reduction X] :
    GrothendieckTopology (affineEtaleSite X) :=
  ReductionData.affineEtaleTopology R.toReductionData

/-- The affine étale topology of a formal algebraic space is the affine étale
topology of its reduction. -/
theorem affineEtaleTopology_def {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X] :
    affineEtaleTopology X = AlgebraicSpace.affineEtaleTopology (reduction X) :=
  rfl

end AlgebraicGeometry.FormalAlgebraicSpace
