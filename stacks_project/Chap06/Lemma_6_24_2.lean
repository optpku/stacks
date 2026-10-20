/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Presheaf TopCat TopCat.Presheaf TopologicalSpace

noncomputable section

universe u

namespace TopCat.Presheaf

/- The site-generic inverse-image functor is the reusable mathlib owner, including for modules over
possibly noncommutative ring presheaves. -/
recall PresheafOfModules.pullback

variable {X Y : TopCat.{u}}
variable (f : X ⟶ Y) (𝒪 : Y.Presheaf CommRingCat.{u})

/- Lemma 6.24.2: under the Stacks convention that rings are commutative with `1`, inverse image
along `f : X ⟶ Y` sends presheaves of `𝒪`-modules functorially to presheaves of
`f_p 𝒪`-modules. -/
@[stacks 008T "inverse image of presheaves of modules along a continuous map"]
#check
  (PresheafOfModules.pullback (commRingPresheafPullbackUnit f 𝒪) :
    PresheafOfModules (ringPresheafOfComm 𝒪) ⥤
      PresheafOfModules (ringPresheafOfComm ((pullback CommRingCat f).obj 𝒪)))

end TopCat.Presheaf
