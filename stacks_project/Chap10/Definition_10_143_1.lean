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

Mathlib owns the global and local etale predicates.  The basic-open
characterization of local etaleness is a neutral ReasLib bridge, so this
chapter file is limited to source-labelled recalls.
-/

/- Definition 10.143.1 (Tag 00U1), global etaleness. -/
@[stacks 00U1 "(1)"]
#check @Algebra.Etale

/- Mathlib owner for local formal etaleness at a prime. -/
#check @Algebra.IsEtaleAt

/- Definition 10.143.1 (Tag 00U1), etaleness at a prime. -/
@[stacks 00U1 "(2)"]
#check @Algebra.isEtaleAt_iff_exists_etale_away
