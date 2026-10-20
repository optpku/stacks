/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Parameters.Perturbation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.126.9

@stack 0BWY

The general stable-completion statement and its reusable perturbation
predicate are owned by the parameter-system leaf.
-/

/- Lemma 15.126.9: complete the head to a parameter system stable under high-order perturbations. -/
@[stacks 0BWY "Lemma 15.126.9, stable parameter completion"]
#check @IsLocalRing.IsSystemOfParameters.exists_cons_stable

#check @IsLocalRing.IsSystemOfParameters.StableUnderHeadPerturbation
#check @IsLocalRing.IsSystemOfParameters.StableUnderHeadPerturbation.isSystemOfParameters
#check @IsLocalRing.IsSystemOfParameters.StableUnderHeadPerturbation.length_eq
