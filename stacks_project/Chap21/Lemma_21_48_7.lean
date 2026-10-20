/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Duality
import StacksCheckRecall

@[expose] public section

/- Lemma 21.48.7 (1) (0FPV): if `ExactPairing M N` exhibits `N` as the Stacks-convention
left dual of `M`, then `M` is perfect. -/
@[stacks 0FPV "(1)"]
#check @RingedSite.Hom.ModuleDerived.IsPerfect.ofExactPairing

/- Lemma 21.48.7 (2) (0FPV): the chosen dual `N` is canonically isomorphic to the
closed-monoidal dual of `M`. -/
@[stacks 0FPV "(2)"]
#check @CategoryTheory.MonoidalClosed.Dual.rightDualIso
