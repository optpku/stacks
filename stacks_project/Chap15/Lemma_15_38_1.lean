/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.Adic.LocalLifting
import StacksCheckRecall

/-!
# Lemma 15.38.1

@stack 0DYG
-/

@[expose] public section

/-! # Lemma 15.38.1: local lifting criteria for formal smoothness -/

/- Lemma 15.38.1, equivalence (1)--(2), tag `0DYG`: maximal-ideal-adic formal smoothness is
equivalent to lifting against the admissible square-zero extensions. -/
@[stacks 0DYG "equivalence (1)-(2), formal smoothness via square-zero local lifts"]
#check @RingHom.MaximalIdealAdic.formallySmooth_iff_hasSquareZeroLifts

/- Lemma 15.38.1, equivalence (1)--(3), tag `0DYG`: for a Noetherian target it is enough to
test the lifting property against small extensions. -/
@[stacks 0DYG "equivalence (1)-(3), formal smoothness via small-extension local lifts"]
#check @RingHom.MaximalIdealAdic.formallySmooth_iff_hasSmallExtensionLifts
