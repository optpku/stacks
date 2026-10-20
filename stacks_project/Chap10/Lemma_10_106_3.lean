/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Regular
public import ReasLib.RingTheory.RegularLocalRing.Parameters.Properties
import StacksCheckRecall

@[expose] public section

/-!
# Regular systems of parameters

Lemma 10.106.3, tag `00NQ`, is split across the reusable parameter-system
and Cohen--Macaulay APIs.  The parameter statements are formulated for the
minimal local-Noetherian assumptions carried by the chosen family; the source
regular-local setting is their direct specialization.

@stack 00NQ
-/

/- Lemma 10.106.3 (1), tag `00NQ`: a regular system of parameters gives a
regular sequence. -/
@[stacks 00NQ "(1)"]
#check @IsLocalRing.IsRegularSystemOfParameters.isRegular

/- Lemma 10.106.3 (2), tag `00NQ`: every initial parameter-ideal quotient is
a regular local ring. -/
@[stacks 00NQ "(2)"]
#check @IsLocalRing.IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal

/- Lemma 10.106.3 (3), tag `00NQ`: the dimension of an initial
parameter-ideal quotient is complementary to its prefix length. -/
@[stacks 00NQ "(3)"]
#check @IsLocalRing.IsSystemOfParameters.ringKrullDim_quotient_parameterIdeal_add_length_eq

/- Lemma 10.106.3 (4), tag `00NQ`: a regular local ring is Cohen--Macaulay
as a module over itself. -/
@[stacks 00NQ "(4)"]
#check @Module.CohenMacaulay.self_of_isRegularLocalRing
