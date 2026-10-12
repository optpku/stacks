/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Flat.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.39.10 (039V): if an `S`-module `M` is flat as an `R`-module and
faithfully flat as an `S`-module, then the algebra map `R → S` is flat.

This is a general descent criterion for a ring map, so its reusable owner is
`RingHom.Flat.of_flat_of_faithfullyFlat` rather than a Chapter 10 declaration.
@stack 039V
-/
@[stacks 039V]
#check @RingHom.Flat.of_flat_of_faithfullyFlat
