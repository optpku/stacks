/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import ReasLib.RingTheory.RingHom.Syntomic.Smooth

@[expose] public section

/-!
# Lemma 10.137.9

@stack 00TA
-/

/-!
# Standard Smooth Cover and Syntomicity Recall

The standard-open cover is already a Mathlib theorem.  The ring-map consequence
belongs to the shared syntomic bridge API.
-/

/- Lemma 10.137.9, tag 00TA: a smooth algebra has a unit-ideal cover by
principal-open standard-smooth localizations. -/
@[stacks 00TA "standard smooth cover"]
#check @Algebra.Smooth.exists_span_eq_top_isStandardSmooth

/- A smooth commutative ring map is syntomic. -/
@[stacks 00TA "smooth ring homomorphisms are syntomic"]
#check @RingHom.Smooth.syntomic

@[stacks 00TA "smooth algebra maps are syntomic"]
#check @Algebra.Smooth.syntomic
