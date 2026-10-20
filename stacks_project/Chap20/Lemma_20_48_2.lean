/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.FlatCokernel
import StacksCheckRecall

@[expose] public section

/- Lemma 20.48.2 (08CH): the boundary cokernel at the lower endpoint of the Tor-amplitude
interval is flat. -/
@[stacks 08CH] #check
  @AlgebraicGeometry.RingedSpace.FlatCokernel.ofTorAmplitudeIn

#check @AlgebraicGeometry.RingedSpace.FlatCokernel.ofTorAmplitudeGE
#check @AlgebraicGeometry.RingedSpace.CochainComplex.isTermwiseFlat_iff
