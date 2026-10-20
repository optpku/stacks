/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.FiniteType.Nilpotent
import StacksCheckRecall

/-!
# Lemma 10.126.8
@stack 0G8U
-/

@[expose] public section

/- Lemma 10.126.8 (Tag 0G8U): if `I` is a nilpotent ideal of `R` and
`S ⧸ I.map (algebraMap R S)` is of finite type over `R ⧸ I`, then `S` is of
finite type over `R`.  The algebra-specialized reusable owner has exactly this
typeclass interface. -/
@[stacks 0G8U]
#check @Algebra.FiniteType.of_quotient_nilpotent

/- Map-first companion for consumers that do not install an ambient algebra. -/
@[stacks 0G8U]
#check @RingHom.FiniteType.of_quotient_nilpotent
