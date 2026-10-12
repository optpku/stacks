/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Single.H0.Exact
import StacksCheckRecall

/-!
# Beauville--Laszlo sequence modulo principal-power torsion

The reusable owner provides the canonical quotient sequence and its
exactness for a Beauville--Laszlo glueing pair.

@stack 0BP4
-/

/- 15.91.16.2: the sequence
`0 → H⁰/H⁰[f^∞] → M₁ → (M')_f/M' → 0` is short exact. -/
@[stacks 0BP4 "15.91.16.2"]
#check @LocalizedModule.Away.FormalGluing.Single.h0TorsionSequence_shortExact_of_glueingPair

#check @LocalizedModule.Away.FormalGluing.Single.h0Torsion
#check @LocalizedModule.Away.FormalGluing.Single.localizedBaseRange
#check @LocalizedModule.Away.FormalGluing.Single.h0TorsionSequence
