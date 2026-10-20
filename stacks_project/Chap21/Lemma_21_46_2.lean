/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.FlatCokernel
import StacksCheckRecall

/-!
# Lemma 21.46.2

The shared owner states the result using the canonical derived Tor-amplitude predicate and keeps
the complex-level exactness formulation as a separate proof-facing entry.
-/

@[expose] public section

/- Lemma 21.46.2 (08G0): the boundary cokernel of a bounded-above termwise-flat representative
at the lower Tor-amplitude bound is flat. -/
@[stacks 08G0] #check
  @SheafOfModules.RingedSite.FlatCokernel.ofTorAmplitudeIn

#check @SheafOfModules.RingedSite.FlatCokernel.ofTorAmplitudeGE
#check @SheafOfModules.RingedSite.FlatCokernel.ofExactAtTensorSingle
#check @HomologicalComplex.IsTermwiseFlat.isFlat_opcycles
#check @CategoryTheory.ShortComplex.isFlat_cokernel_g

end
