/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Uniformizer
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.116.7

The repository path retains the legacy numbering.  The current Stacks entry is Lemma 15.117.7,
tag `09EW`.

The reusable owner separates the finite separable totally ramified field extension from the
distinguished uniformizer and its two congruence formulas.  The latter are carried by
`DVR.UniformizerCongruence`, so downstream arguments can project exactly the equation they need.

@stack 09EW
-/

namespace Lemma_15_116_7

/- Lemma 15.116.7: existence of a totally ramified `p`-power extension with the prescribed
uniformizer congruences. -/
@[stacks 09EW "Lemma 15.116.7: prescribed totally ramified extension"]
#check @DVR.Field.exists_totallyRamified_with_uniformizer

#check @DVR.UniformizerCongruence
#check @DVR.UniformizerCongruence.spec
#check @DVR.UniformizerCongruence.nonempty_iff

end Lemma_15_116_7
