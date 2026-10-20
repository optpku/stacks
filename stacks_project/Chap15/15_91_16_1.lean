module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Single.H0.Exact
import StacksCheckRecall

/-!
# Beauville--Laszlo degree-zero Cech sequence

The reusable owner provides the canonical Cech differential, its kernel, and
the resulting short exact sequence for a Beauville--Laszlo glueing pair.

@stack 0BP3
-/

/- 15.91.16.1: for a Beauville--Laszlo glueing datum, the sequence
`0 → H⁰ → M' ⊕ M₁ → (M')_f → 0` is short exact. -/
@[stacks 0BP3 "15.91.16.1"]
#check @LocalizedModule.Away.FormalGluing.Single.h0Sequence_shortExact_of_glueingPair

#check @LocalizedModule.Away.FormalGluing.Single.Pullback
#check @LocalizedModule.Away.FormalGluing.Single.differential
#check @LocalizedModule.Away.FormalGluing.Single.h0
#check @LocalizedModule.Away.FormalGluing.Single.h0Sequence
