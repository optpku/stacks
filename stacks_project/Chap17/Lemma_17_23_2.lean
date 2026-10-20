/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator.Stalk
import StacksCheckRecall

@[expose] public section

/- Lemma 17.23.2 (0H2J): for a finite-type module sheaf, the stalk ideal of its annihilator
sheaf equals the annihilator ideal of the stalk module. -/
@[stacks 0H2J]
#check @SheafOfModules.Annihilator.stalkIdeal_eq

/- The reverse inclusion is supported by finite-type injectivity of the internal-Hom stalk
comparison. -/
#check @AlgebraicGeometry.RingedSpace.InternalHom.Stalk.comparison_injective
