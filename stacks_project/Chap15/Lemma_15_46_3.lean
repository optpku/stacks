/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.FieldTheory.Subfield.RationalPoints.DirectedIntersection

/-!
# Lemma 15.46.3

@stack 07P3

This chapter file is the `Fin n` source-facing view of the finite-coordinate rational-point
descent owner.  The reusable theorem is stated for an arbitrary finite coordinate type in
`Submodule.RationalPoints`; no chapter-specific `Fin` recursion is exported here.
-/

@[expose] public section

universe u v

variable {K : Type u} [Field K] {A : Type v} {n : ℕ}

/- @stack 07P3 -/
@[stacks 07P3 "Lemma 15.46.3: directed intersection of rational points"]
#check fun (h_nonempty : Nonempty A) (k : Subfield K) (Kα : A → Subfield K)
    (h_inter : k = ⨅ α, Kα α) (h_directed : Directed (· ≥ ·) Kα)
    (V : Submodule K (Fin n → K)) ↦
  Submodule.RationalPoints.exists_ne_zero_iff_of_eq_iInf
    h_nonempty V k Kα h_inter h_directed

#check @Subfield.coordinateSubmodule
#check @Subfield.CoordinateSubmodule.mem_iff
#check @Submodule.rationalPoints
#check @Submodule.RationalPoints.ne_bot_iff_iInf
#check @Submodule.RationalPoints.ne_bot_iff_of_eq_iInf

end
