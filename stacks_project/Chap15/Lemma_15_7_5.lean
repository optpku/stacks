/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Relative
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.7.5

Relative flatness and the induced equivalence of full subcategories are recalled from the
relative pullback-adjunction API.

@stack 07RW
-/

/- Lemma 15.7.5 (1): the fibre-product module of a componentwise flat triple is flat over the
pullback base ring. -/
@[stacks 07RW "Lemma 15.7.5 (1): relative fibre-product flatness"]
#check @FiberProductBaseChangeSituation.RelativeFlat.rightAdjoint_mem

/- Lemma 15.7.5 (2): a relatively flat module is reconstructed by the adjunction unit. -/
@[stacks 07RW "Lemma 15.7.5 (2): relative flat module reconstruction"]
#check @FiberProductBaseChangeSituation.RelativeFlat.unit_isIso

/- Lemma 15.7.5 (3): relative base change is an equivalence on the flat full subcategories. -/
@[stacks 07RW "Lemma 15.7.5 (3): relative equivalence on flat modules"]
#check @FiberProductBaseChangeSituation.RelativeFlat.baseChangeFunctor_isEquivalence

#check @FiberProductBaseChangeSituation.RelativeFlat.moduleProperty
#check @FiberProductBaseChangeSituation.RelativeFlat.ModuleCategory
#check @FiberProductBaseChangeSituation.RelativeFlat.pullbackProperty
#check @FiberProductBaseChangeSituation.RelativeFlat.PullbackCategory
#check @FiberProductBaseChangeSituation.RelativeFlat.baseChangeFunctor
#check @FiberProductBaseChangeSituation.RelativeFlat.rightAdjointFunctor

end
