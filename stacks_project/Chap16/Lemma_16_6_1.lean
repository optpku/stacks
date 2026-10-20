/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.PrincipalThickening.Lift

@[expose] public section

/- Lemma 16.6.1 (tag 07CP): the principal-square lifting theorem and all
quotient comparison maps are owned by ReasLib. -/

@[stacks 07CP]
#check @Algebra.PrincipalThickening.Lift.nonempty

#check @Algebra.PrincipalThickening.Lift
#check @Algebra.PrincipalThickening.Lift.of
#check @Algebra.PrincipalThickening.Lift.spec
#check @Algebra.PrincipalQuotient.Square.mapFirst
#check @Algebra.PrincipalQuotient.Square.reduction
#check @Algebra.PrincipalQuotient.Square.reduction_naturality
#check @Algebra.PrincipalQuotient.FirstOrder.descend
#check @Algebra.PrincipalQuotient.FirstOrder.descend_comp_mk
#check @Module.IsTorsionStable
