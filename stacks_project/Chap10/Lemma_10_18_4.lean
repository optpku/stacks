/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import StacksCheckRecall

/-!
# Lemma 10.18.4

@stack 07BJ
-/

@[expose] public section

/- Lemma 10.18.4: for a ring map `φ : R →+* S` between local rings, the following are
equivalent: `φ` is a local ring homomorphism, the image of the maximal ideal of `R` is contained
in the maximal ideal of `S`, the preimage of the maximal ideal of `S` is the maximal ideal of
`R`, and every element of `R` whose image is a unit in `S` is already a unit in `R`. -/
@[stacks 07BJ "maximal-ideal criteria"]
#check @IsLocalRing.local_hom_TFAE

/- The source's unit-reflection clause is the defining field of `IsLocalHom`. -/
@[stacks 07BJ "unit-reflection clause"]
#check @IsLocalHom.map_nonunit
