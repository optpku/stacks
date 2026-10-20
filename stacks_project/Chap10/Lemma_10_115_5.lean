/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Away
import StacksCheckRecall

/-!
# Local Noether Normalization on a Basic Open

@stack 00OZ
-/

/- Lemma 10.115.5: a local Noether normalization exists on a basic-open
neighborhood of every point. -/
@[stacks 00OZ]
#check @MvPolynomial.NoetherNormalization.Away.exists_at_point

@[stacks 00OZ "witness data"]
#check @MvPolynomial.NoetherNormalization.Away.IsAtPoint

@[stacks 00OZ "witness specification"]
#check @MvPolynomial.NoetherNormalization.Away.isAtPoint_iff
