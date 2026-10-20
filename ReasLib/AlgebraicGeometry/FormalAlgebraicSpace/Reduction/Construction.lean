module

public import ReasLib.AlgebraicGeometry.Presheaf.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The reduced subsheaf of a locally Noetherian formal algebraic space,
viewed as an algebraic space. -/
def reductionSpace {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    [formalSpace : IsFormalAlgebraicSpace F] [IsLocallyNoetherian F] :
    AlgebraicSpace S :=
  AlgebraicSpace.ofFunctor (SpacePresheaf.reduction F).toFunctor
    (SpacePresheaf.reduction_isSheaf F formalSpace.isSheaf) sorry sorry

/-- The reduced subsheaf and its inclusion give reduction data for a locally
Noetherian formal algebraic space. -/
def reductionData {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    [formalSpace : IsFormalAlgebraicSpace F] [IsLocallyNoetherian F] :
    ReductionData F where
  space := reductionSpace F
  ι := (SpacePresheaf.reduction F).ι
  isReduced := sorry
  representable := sorry
  isThickening := sorry
  liftUnique := sorry

end AlgebraicGeometry.FormalAlgebraicSpace
