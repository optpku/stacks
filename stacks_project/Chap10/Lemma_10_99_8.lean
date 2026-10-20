/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.Tor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.99.8

@stack 051C
-/

/- Lemma 10.99.8 (1): quotient flatness modulo `I` and vanishing of
`Tor₁^R(R ⧸ I, M)` give flatness modulo every positive power of `I`. -/
@[stacks 051C "(1)"]
#check @Module.Flat.quotient_pow_of_quotient_flat_of_isZero_tor_one

/- Lemma 10.99.8 (2): under the same hypotheses, `Tor₁^R(N, M)` vanishes when a power of `I`
annihilates `N`. -/
@[stacks 051C "(2)"]
#check @Module.Flat.isZero_tor_one_of_annihilated_by_ideal_pow

/- Lemma 10.99.8 (3): if `I` is nilpotent, the same hypotheses imply `Module.Flat R M`. -/
@[stacks 051C "(3)"]
#check @Module.Flat.of_isNilpotent_ideal_of_quotient_flat_of_isZero_tor_one
