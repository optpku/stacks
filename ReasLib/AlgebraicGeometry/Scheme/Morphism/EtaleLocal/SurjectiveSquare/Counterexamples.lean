module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.SurjectiveSquare
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianTarget.Counterexample
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NoetherianAtSpecializations.Counterexample

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace LocallyNoetherianTarget

/-- Having locally Noetherian target is invariant in commutative squares whose vertical
maps are surjective and étale. -/
instance isEtaleLocalInSurjectiveSquares :
    IsEtaleLocalInSurjectiveSquares
      (LocallyNoetherianTarget : MorphismProperty Scheme.{u}) := sorry

/-- Invariance in surjective étale squares does not imply étale locality on
source-and-target, as witnessed by the property of having locally Noetherian target. -/
theorem notIsEtaleLocalAtSourceAndTarget :
    ¬ IsEtaleLocalAtSourceAndTarget
      (LocallyNoetherianTarget : MorphismProperty Scheme.{0}) := sorry

end LocallyNoetherianTarget

namespace NoetherianAtSpecializations

/-- Separate étale locality on the source and target does not imply invariance in
surjective étale squares, as witnessed by being Noetherian at specializations. -/
theorem notIsEtaleLocalInSurjectiveSquares :
    ¬ IsEtaleLocalInSurjectiveSquares
      (NoetherianAtSpecializations : MorphismProperty Scheme.{0}) := sorry

end NoetherianAtSpecializations

end AlgebraicGeometry
