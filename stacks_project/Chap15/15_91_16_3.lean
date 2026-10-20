/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Single.H0.Exact
import StacksCheckRecall

/-!
# Base change of the Beauville--Laszlo mod-torsion sequence

The reusable owner provides the literal base-changed sequence and its
exactness for a Beauville--Laszlo glueing pair.

@stack 0BP5
-/

/- 15.91.16.3: the sequence
`0 → R' ⊗[R] (H⁰/H⁰[f^∞]) → (M')_f → (M')_f/M' → 0` is short exact. -/
@[stacks 0BP5 "15.91.16.3"]
#check @LocalizedModule.Away.FormalGluing.Single.BaseChange.sequence_shortExact_of_glueingPair

#check @LocalizedModule.Away.FormalGluing.Single.BaseChange.leftMap
#check @LocalizedModule.Away.FormalGluing.Single.BaseChange.rightMap
#check @LocalizedModule.Away.FormalGluing.Single.BaseChange.sequence
