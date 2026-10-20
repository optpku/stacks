/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Stalks.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat
open scoped TopCat

universe u

namespace TopCat.Sheaf

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒢 : Y.Sheaf (Type u)) (x : X)

/- Lemma 6.21.5: for a continuous map `f : X ⟶ Y`, a sheaf of sets `𝒢` on `Y`, and a point
`x : X`, the canonical bijection of stalks is the `Type u` specialization of the reusable
sheaf-pullback stalk isomorphism. -/
@[stacks 008H "stalks of inverse-image sheaves of sets"]
#check
  (stalkPullbackIso f 𝒢 x :
    𝒢.presheaf.stalk (f x) ≅ ((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf.stalk x)

end

end TopCat.Sheaf
