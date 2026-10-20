/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Resolution.PrincipalAnnihilator.Factorisation

@[expose] public section

/- Lemma 16.7.1 is the source-facing existence view of the reusable bundled
principal-annihilator factorisation API. -/
@[stacks 07CR]
#check @Algebra.PrincipalAnnihilator.Factorisation.nonempty_of_exists

#check @Algebra.PrincipalAnnihilator.Factorisation
#check @AlgHom.Factorisation.Finite.BaseControl
#check @Algebra.PrincipalAnnihilator.Factorisation.nonempty
#check @Algebra.PrincipalAnnihilator.Factorisation.spec
#check @Module.torsionStepAnnihilator
#check @Module.self_mem_torsionStepAnnihilator
#check @Module.IsTorsionStable
#check @Submodule.TorsionStep
#check @Algebra.PrincipalQuotient.map
