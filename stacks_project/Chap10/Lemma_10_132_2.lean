/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Descent
import StacksCheckRecall

@[expose] public section

/-!
# Descent of the algebraic de Rham complex

@stack 07HY

The reusable descent construction belongs to
`DifferentialOperator.DeRham.Family.existsDescended`.  This source-facing file
specializes it to the universal Kähler derivation and discharges its spanning
hypothesis through `KaehlerDifferential.span_range_derivation`.
-/

/- Lemma 10.132.2, tag 07HY: a surjective quotient of `Ω[B⁄A]` satisfying the
degree-one kernel condition inherits a de Rham differential family. -/
@[stacks 07HY]
#check @KaehlerDifferential.DeRham.existsDescended

@[stacks 07HY "generic descent criterion"]
#check @DifferentialOperator.DeRham.Family.existsDescended

@[stacks 07HY "kernel condition"]
#check @DifferentialOperator.DeRham.KernelCondition

@[stacks 07HY "universal derivation spans Kähler differentials"]
#check @KaehlerDifferential.span_range_derivation
