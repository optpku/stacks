/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Neighborhood.LocalConsequences
import StacksCheckRecall

@[expose] public section

/-! @stack 00U1 -/

/-!
# Definition 10.143.1

Mathlib owns global etaleness and the formal stalk predicate. ReasLib
specializes `RingHom.AtPrime` to etaleness on a principal-open neighborhood
for arbitrary ring maps, as in the source. Finite presentation identifies
this local condition with Mathlib's formal stalk predicate.
-/

/- Definition 10.143.1 (Tag 00U1), global etaleness. -/
@[stacks 00U1 "(1)"]
#check @Algebra.Etale

/- Mathlib owner for local formal etaleness at a prime. -/
#check @Algebra.IsEtaleAt

/- Definition 10.143.1 (Tag 00U1), etaleness at a prime. -/
@[stacks 00U1 "(2)"]
#check @Algebra.EtaleAtPrime

@[stacks 00U1 "(2) principal-open criterion"]
#check @Algebra.EtaleAtPrime.iff_exists_away

/- Comparison with the formal stalk predicate under finite presentation. -/
#check @Algebra.EtaleAtPrime.iff_isEtaleAt
#check @Algebra.isEtaleAt_iff_exists_etale_away
