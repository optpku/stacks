/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Regular.JRing
import StacksCheckRecall

/-!
# Definition 15.47.1

@stack 07P7
-/

@[expose] public section

/- Definition 15.47.1 (1): `J-0` rings. -/
@[stacks 07P7 "(1)"]
#check @IsJ0Ring

/- Definition 15.47.1 (2): `J-1` rings. -/
@[stacks 07P7 "(2)"]
#check @IsJ1Ring

/- Definition 15.47.1 (3): `J-2` rings. -/
@[stacks 07P7 "(3)"]
#check @IsJ2Ring

#check @PrimeSpectrum.regularLocus
#check @isJ0Ring_iff_exists_nonempty_open_subset_regularLocus
#check @isJ1Ring_iff_regularLocus_isOpen
#check @isJ2Ring_iff_forall_finiteType_isJ1
