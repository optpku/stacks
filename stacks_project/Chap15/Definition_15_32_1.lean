/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Ideal.QuasiRegular

/-!
# Definition 15.32.1

@stack 07CV
-/

@[expose] public section

/- Definition 15.32.1 (1), tag `07CV`: regular ideals. -/
@[stacks 07CV "Definition 15.32.1 (1), regular ideals"]
#check @Ideal.IsRegularIdeal

/- Definition 15.32.1 (2), tag `07CV`: Koszul-regular ideals. -/
@[stacks 07CV "Definition 15.32.1 (2), Koszul-regular ideals"]
#check @Ideal.IsKoszulRegularIdeal

/- Definition 15.32.1 (3), tag `07CV`: `H1`-regular ideals. -/
@[stacks 07CV "Definition 15.32.1 (3), H1-regular ideals"]
#check @Ideal.IsH1RegularIdeal

/- Definition 15.32.1 (4), tag `07CV`: quasi-regular ideals. -/
@[stacks 07CV "Definition 15.32.1 (4), quasi-regular ideals"]
#check @Ideal.IsQuasiRegularIdeal
