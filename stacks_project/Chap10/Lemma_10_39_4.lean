/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.39.4

@stack 00HC
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.39.4: compositions of flat ring homomorphisms are flat. -/
@[stacks 00HC "composition of flat maps"]
#check @RingHom.Flat.comp

/- Companion recall: compositions of faithfully flat ring homomorphisms are faithfully flat.
Mathlib packages this as stability under composition of `RingHom.FaithfullyFlat`. -/
@[stacks 00HC "composition of faithfully flat maps"]
#check @RingHom.FaithfullyFlat.stableUnderComposition

/- Companion recall: if `R → R'` is flat and `M'` is a flat `R'`-module, then `M'` is flat as an
`R`-module. -/
@[stacks 00HC "flat module transitivity"]
#check @Module.Flat.trans

/- Companion recall: if `R → R'` is faithfully flat and `M'` is a faithfully flat `R'`-module,
then `M'` is faithfully flat as an `R`-module. -/
@[stacks 00HC "faithfully flat module transitivity"]
#check @Module.FaithfullyFlat.trans
