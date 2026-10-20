/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.IdealPower.TorsionQuotient

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits

namespace Ideal

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable (I : Ideal A)

/- Exercise 111.43.10 (1): writing `M' = M ⧸ I.primaryComponent M` for the quotient by the
`I`-power torsion submodule `I.primaryComponent M`, the `I`-power torsion of `M'` is zero:
`I.primaryComponent M' = ⊥`. -/
@[stacks 0DAT]
#check (Ideal.primaryComponent_quotient_eq_bot I :
    I.primaryComponent (M ⧸ I.primaryComponent M) = ⊥)

/- Exercise 111.43.10 (2): writing `M' = M ⧸ I.primaryComponent M`, the canonical morphism
`colim.map (I.powerHomModuleDiagramMap (Submodule.mkQ (I.primaryComponent M)))` identifies
the sequential colimits of `Hom_A(I^n, M)` and `Hom_A(I^n, M')`. -/
@[stacks 0DAT]
#check (Ideal.instIsIso_colimMap_powerHomModuleDiagramMap_mkQ I :
    IsIso (colim.map (I.powerHomModuleDiagramMap (Submodule.mkQ (I.primaryComponent M)))))

end Ideal
