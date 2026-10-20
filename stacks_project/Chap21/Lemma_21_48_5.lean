/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Monoidal
import StacksCheckRecall

@[expose] public section

/- Lemma 21.48.5 (0FPT): the canonical K-flat derived tensor product makes the derived category
of modules on a commutative ringed site symmetric monoidal. -/
@[stacks 0FPT]
#check @RingedSite.Hom.ModuleDerived.symmetricCategory

#check @RingedSite.Hom.ModuleDerived.monoidalCategory
