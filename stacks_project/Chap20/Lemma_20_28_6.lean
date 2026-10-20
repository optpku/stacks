/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
import StacksCheckRecall

@[expose] public section

/- [stacks 0FP1] Lemma 20.28.6: the underived and derived counits are compatible with the
canonical comparison maps for a morphism of ringed spaces. -/

namespace AlgebraicGeometry.RingedSpace

#check @modulePullbackDerivedPushforwardAdjunction
#check @modulePullbackDerived_isLeftAdjoint
@[stacks 0FP1] #check @CategoryTheory.Adjunction.derivedε_fac_app

end AlgebraicGeometry.RingedSpace
