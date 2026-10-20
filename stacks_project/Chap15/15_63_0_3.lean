/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Pairing
import StacksCheckRecall

/-!
# Equation 15.64.0.3 (068J)

Repository source label: 15.63.0.3.

The Tor pairing and its chain-level augmentation are owned by
`CategoryTheory.ModuleCat.Tor.Pairing`.  This file is the source-facing recall.

@stack 068J
-/

@[expose] public section

/- Equation 15.64.0.3 (068J):
`Tor^R_n(M, A) ⊗[A] Tor^R_m(N, A) ⟶ Tor^R_{n+m}(M ⊗[R] N, A)`. -/
@[stacks 068J "canonical Tor pairing"]
#check @CategoryTheory.ModuleCat.Tor.Pairing.pairing

#check @CategoryTheory.ModuleCat.Tor.Pairing.obj
#check @CategoryTheory.ModuleCat.Tor.Pairing.pairingOf
#check @CategoryTheory.ModuleCat.Tor.Pairing.singleTensorComponent
#check @CategoryTheory.ModuleCat.Tor.Pairing.singleTensorComplexMap
#check @CategoryTheory.ModuleCat.Tor.Pairing.singleTensorComparison
#check @CategoryTheory.ModuleCat.Tor.Pairing.scalarExtensionTensorComparison

#print axioms CategoryTheory.ModuleCat.Tor.Pairing.singleTensorComponent
#print axioms CategoryTheory.ModuleCat.Tor.Pairing.singleTensorComplexMap
#print axioms CategoryTheory.ModuleCat.Tor.Pairing.singleTensorComparison
#print axioms CategoryTheory.ModuleCat.Tor.Pairing.scalarExtensionTensorComparison
#print axioms CategoryTheory.ModuleCat.Tor.Pairing.pairingOf
#print axioms CategoryTheory.ModuleCat.Tor.Pairing.pairing
