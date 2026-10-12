/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flat.FaithfullyFlat.Injective
import StacksCheckRecall

@[expose] public section

universe u

/- Remark 35.4.27: No faithfully flat commutative `ℤ`-algebra is injective as a
`ℤ`-module. -/
@[stacks 08XF] #check
  (Module.FaithfullyFlat.not_injective_int :
    ∀ (T : Type u) [CommRing T] [Module.FaithfullyFlat ℤ T], ¬ Module.Injective ℤ T)
