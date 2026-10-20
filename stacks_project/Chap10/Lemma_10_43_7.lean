/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.MinimalPrime
import StacksCheckRecall

@[expose] public section

/-!
# Geometric Reducedness at Minimal Primes

Lemma 10.43.7 is a canonical recall of the shared minimal-prime localization
criterion for `Algebra.IsGeometricallyReduced`.

@stack 07K2
-/

/- Lemma 10.43.7 (Tag 07K2): a reduced algebra over a field is geometrically reduced when all
of its localizations at minimal primes are geometrically reduced. -/
@[stacks 07K2]
#check @Algebra.IsGeometricallyReduced.of_forall_minimalPrimes_localization

@[stacks 07K2 "minimal-prime localization companion"]
#check @Algebra.IsGeometricallyReduced.of_forall_minimalPrimes_localization_of
