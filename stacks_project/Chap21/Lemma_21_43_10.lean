/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticPullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 21.43.10 (0GZ1): for the morphism of chaotic ringed topoi induced by
`u : C₁ ⥤ C₀` and `gSharp : g⁻¹O ⟶ O'`, the canonical derived inverse image maps
`Chaotic.QC O` into `Chaotic.QC O'`. -/
@[stacks 0GZ1]
#check @CategoryTheory.ModulesOnCategory.Chaotic.Pullback.mapsTo

#check @RingedSite.Chaotic.toposHom
#check @RingedSite.Chaotic.derivedPullback
#check @CategoryTheory.ModulesOnCategory.Chaotic.Pullback.functor
#check @CategoryTheory.ModulesOnCategory.Chaotic.Pullback.compιIso
