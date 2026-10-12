/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.RegularSequence.LocalHom
import StacksCheckRecall

@[expose] public section

/-!
# Lifting a maximal regular sequence along a local homomorphism

@stack 06LC

The local-homomorphism theorem is owned by `Module.CohenMacaulay`; this entry
records its Stacks source contract.
-/

/- Lemma 10.104.10: let `φ : A →+* B` be a local homomorphism of local rings. If `B`
is Noetherian and Cohen--Macaulay and its maximal ideal is the radical of the extension of
the maximal ideal of `A`, then a sequence of `dim(B)` elements of `A` maps to a regular
sequence in `B`. -/
@[stacks 06LC]
#check @Module.CohenMacaulay.exists_regularSequence_map_of_radical_maximalIdeal
