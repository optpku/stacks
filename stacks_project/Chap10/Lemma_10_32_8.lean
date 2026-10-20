/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.OneAdd.LocallyNilpotent
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.32.8

The reusable owner is `Ideal.IsLocallyNilpotent.oneAdd_pow_bijective` together
with its unit-valued quotient-root companion. The canonical submonoid
`I.oneAdd` directly models `1 + I`; no coordinate reparameterization is introduced.

@stack 0CAP
-/

/- Lemma 10.32.8 (1): for `1 ≤ n` whose image is a unit modulo a locally
nilpotent ideal, the `n`-th power map on `1 + I` is bijective. -/
@[stacks 0CAP "(1), power bijection on oneAdd"]
#check @Ideal.IsLocallyNilpotent.oneAdd_pow_bijective

#check @Ideal.IsLocallyNilpotent.oneAdd_existsUnique_pow_eq

/- Lemma 10.32.8 (2): a unit is an nth power exactly when its quotient image
is an nth power. -/
@[stacks 0CAP "(2), unit-valued quotient root criterion"]
#check @Ideal.IsLocallyNilpotent.units_exists_pow_iff_quotient

#check @Ideal.IsLocallyNilpotent.isUnit_exists_pow_iff_quotient
