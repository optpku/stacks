/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

/-- Direct image of commutative-ring sheaves along a continuous map is a right adjoint at
the continuous-site functor presentation. -/
instance commRingPushforwardContinuousIsRightAdjoint {X Y : TopCat.{u}} (f : X ⟶ Y) :
    ((TopologicalSpace.Opens.map f).sheafPushforwardContinuous CommRingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).IsRightAdjoint :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).isRightAdjoint

end TopCat.Sheaf
