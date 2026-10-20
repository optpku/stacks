/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.Pullback
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.46.5

Tor-amplitude preservation under derived pullback is owned by the commutative ringed-site
specialization in `ReasLib`; this file only records the tagged source entry.
-/

/- Lemma 21.46.5 (08H5): derived pullback preserves every fixed Tor-amplitude interval. -/
@[stacks 08H5]
#check @RingedSite.Hom.modulePullbackDerived_hasTorAmplitudeIn

#check @RingedSite.Hom.modulePullbackDerived_hasFiniteTorDimension

end
