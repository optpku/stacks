/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.FinitePresentation

/-!
# Lemma 15.59.9

@stack 0E8F

The finitely-presented-module criterion is owned by
`CochainComplex.isKFlat_of_tensor_finitelyPresented_acyclic`.
-/

@[expose] public section

/- Lemma 15.59.9 (0E8F): tensor-acyclicity against finitely presented modules detects
K-flatness. -/
@[stacks 0E8F "detecting K-flatness on finitely presented modules"]
#check @CochainComplex.isKFlat_of_tensor_finitelyPresented_acyclic
