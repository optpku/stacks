/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.IndSmooth.SquareZero.Killing

@[expose] public section

/- Lemma 16.5.2 (tag 07CL): the ideal-killing factorization through a smooth
algebra is owned by ReasLib. -/

@[stacks 07CL]
#check @AlgHom.Factorisation.Smooth.Killing.nonempty_of_squareZero

#check @AlgHom.Factorisation.Smooth.Killing
#check @AlgHom.Factorisation.Smooth.Killing.of
#check @AlgHom.Factorisation.Smooth.Killing.spec
