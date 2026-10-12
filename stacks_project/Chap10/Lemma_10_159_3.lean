/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.ResidueField.FiniteFree
import StacksCheckRecall

/-!
# Finite-free residue-field realizations

@stack 07NE

The canonical owner exposes the concrete finite-free algebra, its extended
prime, and the residue-field `AlgEquiv`.
-/

@[expose] public section

@[stacks 07NE "finite-free residue-field realization"]
#check @Ideal.ResidueField.exists_finiteFree_realization
