/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf TopCat

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {𝒪 𝒪' : X.Sheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
variable (ℱ : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)) (x : X)

/- Lemma 6.20.3: the canonical comparison
`ℱ_x ⊗[𝒪_x] 𝒪'_x ⟶ (ℱ ⊗_𝒪 𝒪')_x` is an isomorphism of `𝒪'_x`-modules. -/
@[stacks 008B]
#check sheafModuleBaseChangeComparisonIso p ℱ x

end TopCat.Sheaf
