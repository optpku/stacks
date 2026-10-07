module

public import ReasLib.AlgebraicGeometry.WeilCohomology.CycleClass.ClosedSubscheme

@[expose] public section

namespace WeilCohomology

open AlgebraicGeometry CategoryTheory

#check (effectiveCartierDivisorPicardClass :
  ∀ {Y X : Scheme} (i : Y ⟶ X), IsEffectiveCartierDivisor i → X.PicardGroup)

end WeilCohomology
