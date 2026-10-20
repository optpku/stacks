/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk
import StacksCheckRecall

@[expose] public section

/- Lemma 20.48.5: an object `E` of `D(𝒪_X)` has tor-amplitude in `[a, b]` if and only if
the derived stalk `E_x` has tor-amplitude in `[a, b]` for every point `x : X`.  The public
owner uses the canonical ringed-space module stalk and its derived functor directly. -/
@[stacks 09U9]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk.hasTorAmplitudeIn_iff

#check @AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk.functor
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk.obj
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk.HasTorAmplitudeIn.forall_stalk
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk.HasTorAmplitudeIn.of_forall_stalk
