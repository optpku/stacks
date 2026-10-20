/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FormalFiber.GeometricallySerre
import StacksCheckRecall

/-!
# Lemma 15.51.13

@stack 0BIZ
-/

@[expose] public section

/- Lemma 15.51.13: geometric Serre condition `(R_n)` satisfies all five formal-fiber
permanence laws. -/
@[stacks 0BIZ "geometric Serre R formal-fiber laws"]
#check @FieldAlgebraProperty.geometricallySerreR.formalFiberLaws

#synth (FieldAlgebraProperty.geometricallySerreR 0).EssFiniteTypeBaseChange
#synth (FieldAlgebraProperty.geometricallySerreR 0).IsLocal
#synth (FieldAlgebraProperty.geometricallySerreR 0).RegularFiberAscent
#synth (FieldAlgebraProperty.geometricallySerreR 0).FaithfullyFlatDescent
#synth (FieldAlgebraProperty.geometricallySerreR 0).SeparableExtension
