/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

universe w v u

noncomputable section

section

variable [UnivLE.{w, u}]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable (𝒪 : TopCat.Sheaf CommRingCat.{u} X)
variable (ℱ : SheafOfModules.{v} (TopCat.Sheaf.ringSheafOfComm 𝒪))

/- The site-generic functor `SheafOfModules.pushforward` is the canonical data owner, while
`TopCat.Sheaf.pushforward` identifies its target ring sheaf for a continuous map. The identity
map on that direct-image ring sheaf recovers exactly the source specialization, so no local
wrapper or stronger ringed-space hypothesis is needed. -/
/- Lemma 6.24.5: under the Stacks convention that rings are commutative with `1`, the direct image
of a sheaf of `𝒪`-modules along `f` is a sheaf of modules over `f_* 𝒪`. -/
@[stacks 008W "direct image of a sheaf of modules along a continuous map"]
#check
  (SheafOfModules.pushforward
    (TopCat.Sheaf.commRingSheafPushforwardId f 𝒪)).obj ℱ

end
