/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Sheaf TopCat TopCat.Sheaf TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}

variable (f : X ⟶ Y) (𝒪 : Y.Sheaf CommRingCat.{u})
variable (𝒢 : SheafOfModules (TopCat.Sheaf.ringSheafOfComm.{u, u} 𝒪))

/- Lemma 6.24.6: under the Stacks convention that rings are commutative with `1`, inverse image
sends a sheaf of `𝒪`-modules to a sheaf of `f⁻¹𝒪`-modules. -/
@[stacks 008X "inverse image module structure along a continuous map"]
#check
  (SheafOfModules.pullback
      (commRingSheafPullbackUnit f 𝒪)).obj 𝒢

end TopCat.Sheaf
