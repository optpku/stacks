/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.FieldTheory.RatFunc.FieldExtension
public import ReasLib.RingTheory.Spectrum.Prime.Irreducible
public import ReasLib.RingTheory.Spectrum.Prime.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.47.10 support index

This index keeps the historical import path while exposing the neutral PrimeSpectrum and RatFunc
owners used by the chapter statement.

@stack 00I7
@stack 0G31
-/

@[stacks 00I7 "irreducibility and the unique minimal prime"]
#check @PrimeSpectrum.irreducible_iff_unique_minimalPrime

@[stacks 0G31 "rational-function scalar extension"]
#check @RatFunc.FieldExtension.map

end
