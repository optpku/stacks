/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Duality
import StacksCheckRecall

@[expose] public section

/- Lemma 21.48.4 (1) (08JJ): the closed-monoidal dual of a perfect derived module sheaf is
perfect. -/
@[stacks 08JJ "(1)"]
#check @RingedSite.Hom.ModuleDerived.IsPerfect.dual

/- Lemma 21.48.4 (2) (08JJ): the canonical bidual comparison of a perfect derived module sheaf
is invertible. -/
@[stacks 08JJ "(2)"]
#check @RingedSite.Hom.ModuleDerived.IsPerfect.isIso_bidualComparison

/- Lemma 21.48.4 (3) (08JJ): tensoring with the dual of a perfect object computes its internal
Hom functor. -/
@[stacks 08JJ "(3)"]
#check @RingedSite.Hom.ModuleDerived.IsPerfect.isIso_tensorComparison

#check @CategoryTheory.MonoidalClosed.Dual.tensorComparison
#check @CategoryTheory.MonoidalClosed.Dual.tensorComparisonNatTrans

/- Lemma 21.48.4 (4) (08JJ): the degree-zero tensor-dual comparison is bijective. -/
@[stacks 08JJ "(4)"]
#check @RingedSite.Hom.ModuleDerived.IsPerfect.homComparison_bijective

#check @CategoryTheory.MonoidalClosed.Dual.homComparison
