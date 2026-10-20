/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.CycleClass.ClosedSubscheme

@[expose] public section

namespace WeilCohomology

open AlgebraicGeometry CategoryTheory

#check (effectiveCartierDivisorPicardClass :
  ∀ {Y X : Scheme} (i : Y ⟶ X), IsEffectiveCartierDivisor i → X.PicardGroup)

end WeilCohomology
