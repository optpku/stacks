/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Functors

@[expose] public section

open CategoryTheory TopCat

universe u

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The inverse-image functor on sheaves of sets is left adjoint to direct image. -/
noncomputable def typesPullbackPushforwardAdjunction :
    pullback (Type u) f ⊣ pushforward (Type u) f :=
  pullbackPushforwardAdjunction (Type u) f

end TopCat.Sheaf
