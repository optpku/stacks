/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Localization
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Local
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.66.2

The localization criterion for weakly associated primes is owned by the
localization leaf in ReasLib, while its `(2) ↔ (3)` clause is generalized to
all local rings in `Ideal.IsWeaklyAssociatedToModule.Local`.  This chapter
file is only the source-labelled recall surface; keeping the clauses as
separate checks makes each direction available without a chapter-local alias.

@stack 0566
-/

/- Lemma 10.66.2 (Tag 0566), clauses `(1) ↔ (2)`. -/
@[stacks 0566 "(1) ↔ (2)"]
#check @Ideal.IsWeaklyAssociatedToModule.Localization.iff_maximalIdeal

/- Lemma 10.66.2 (Tag 0566), clauses `(1) ↔ (3)`. -/
@[stacks 0566 "(1) ↔ (3)"]
#check @Ideal.IsWeaklyAssociatedToModule.Localization.iff_associatedPrime

/- Lemma 10.66.2 (Tag 0566), source-facing `AtPrime` clauses `(2) ↔ (3)`. -/
@[stacks 0566 "(2) ↔ (3)"]
#check @Ideal.IsWeaklyAssociatedToModule.Localization.maximalIdeal_iff_associatedPrime_atPrime

/- Generic companion: the same comparison for any local ring. -/
#check @Ideal.IsWeaklyAssociatedToModule.Local.maximalIdeal_iff_associatedPrime
