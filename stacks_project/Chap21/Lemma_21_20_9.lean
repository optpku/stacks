/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization.ProjectionFormula
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.9

Derived extension by zero satisfies the projection formula with one local factor and one
ambient factor.  The ambient factor is restricted to the slice on the right-hand side.
-/

/- Lemma 21.20.9 (0GL1): for `L ∈ D(O|_U)` and `K ∈ D(O)`,
`j_!L ⊗ᴸ K ≅ j_!(L ⊗ᴸ K|_U)`. -/
@[stacks 0GL1]
#check @SheafOfModules.RingedSite.Localization.DerivedAdjunction.projectionFormula

#check @CategoryTheory.Adjunction.DerivedProjectionFormula
#check @CategoryTheory.Adjunction.DerivedProjectionFormula.isomorphic
#check @SheafOfModules.RingedSite.Localization.lowerShriekDerived
#check @SheafOfModules.RingedSite.Localization.restrictionDerived
