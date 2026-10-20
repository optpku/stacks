/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Homotopy.Cofiber
import StacksCheckRecall

/-!
# The Koszul cofiber comparison for a product scalar

@stack 062B
-/

@[expose] public section

/- Lemma 15.28.10: adjoining multiplication by `f * g` gives a Koszul complex homotopy
equivalent to the cofiber of a map from the shifted `f`-complex to the `g`-complex. -/
@[stacks 062B "Lemma 15.28.10"]
#check @KoszulComplex.coprodScalarMul_exists_homotopyEquiv

#check @ChainComplex.homotopyCofiber.exists_homotopyEquiv_smul_mul
