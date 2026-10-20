/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
import StacksCheckRecall

@[expose] public section

/- Definition 20.48.1 (1), (2), and (4): the ringed-space Tor-amplitude, finite-Tor-dimension,
and module Tor-dimension predicates are the canonical specializations owned by ReasLib. -/
@[stacks 08CG "(1)"] #check AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn
@[stacks 08CG "(2)"] #check AlgebraicGeometry.RingedSpace.HasFiniteTorDimension
@[stacks 08CG "(4)"] #check AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE

#check AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_iff
#check AlgebraicGeometry.RingedSpace.hasFiniteTorDimension_iff
#check AlgebraicGeometry.RingedSpace.moduleHasTorDimensionLE_iff
