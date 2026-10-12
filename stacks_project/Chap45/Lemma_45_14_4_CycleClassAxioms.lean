/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.CycleClass.ClosedSubscheme

@[expose] public section

namespace WeilCohomology

open AlgebraicGeometry CategoryTheory

#check (effectiveCartierDivisorPicardClass :
  ∀ {Y X : Scheme} (i : Y ⟶ X), IsEffectiveCartierDivisor i → X.PicardGroup)

end WeilCohomology
