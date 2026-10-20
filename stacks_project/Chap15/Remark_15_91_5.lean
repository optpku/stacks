/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.BeauvilleLaszlo.Counterexample
import StacksCheckRecall

/-!
# Remark 15.91.5

Localization away from one element is always flat, whereas principal-adic
completion need not be flat without Noetherian hypotheses.  Consequently the
usual faithfully flat descent datum, involving a completion tensor square, is
not the formalism used in this section.

@stack 0BNP
-/

@[expose] public section

universe u

namespace Remark_15_91_5

variable {R : Type u} [CommRing R] (f : R)

/- Remark 15.91.5 (0BNP): localization away from `f` is flat over `R`. -/
@[stacks 0BNP "away localization is flat"]
#check (inferInstance : Module.Flat R (Localization.Away f))

variable [IsNoetherianRing R]

/- Under the Noetherian hypothesis, the principal-adic completion is flat. -/
@[stacks 0BNP "Noetherian principal-adic completion is flat"]
#check (inferInstance : Module.Flat R (principalAdicCompletion f))

/- Without the Noetherian hypothesis, explicit principal-adic completion maps
can fail to be flat. -/
@[stacks 0BNP "principal-adic completion need not be flat"]
#check @firstBeauvilleLaszloCounterexample_completion_not_flat

end Remark_15_91_5
