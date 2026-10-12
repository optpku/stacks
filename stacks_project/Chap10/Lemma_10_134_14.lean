/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.Stability
import StacksCheckRecall

/-!
@stack 00S3
-/

@[expose] public section

/- Lemma 10.134.14 [stacks 00S3]: canonical recall of the stable biproduct
isomorphism induced by a homotopy equivalence of chain complexes concentrated
in degrees `0` and `1`.  The reusable owner is the neutral
`CategoryTheory.ChainComplex.HomotopyEquiv` API. -/
@[stacks 00S3]
#check @CategoryTheory.ChainComplex.HomotopyEquiv.stableBiprodHom_isIso_of_concentrated

#check @CategoryTheory.ChainComplex.HomotopyEquiv.toShortComplex
#check @CategoryTheory.ChainComplex.HomotopyEquiv.stableBiprodHom
#check @CategoryTheory.ChainComplex.HomotopyEquiv.stableBiprodInv
#check @CategoryTheory.ChainComplex.HomotopyEquiv.stableBiprodIso
