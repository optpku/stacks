/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.BoundedAbove
import StacksCheckRecall

@[expose] public section

/- Lemma 20.47.7 (09V7): a locally bounded-above complex with the expected termwise
pseudo-coherence bounds is `m`-pseudo-coherent. -/
@[stacks 09V7]
#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedAbove.isMPseudoCoherent

-- The global bounded-above case and passage to the derived category use these atomic bridges.
#check @AlgebraicGeometry.RingedSpace.CochainComplex.isLocallyBoundedAbove_of_minus
#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedAbove.q_obj
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.of_representation
