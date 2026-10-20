/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence.Tor
import StacksCheckRecall

/-!
# Tor spectral sequences of a bounded-below chain complex

This chapter file recalls the canonical Tor spectral-sequence API from `ReasLib`.

@stack 061Z
-/

@[expose] public section

/- Example 15.62.1 (1), tag `061Z`: the first spectral sequence has page two
`Tor_j^R(H_i(K),M)` and converges to derived tensor homology. -/
@[stacks 061Z "(1) homology-first Tor spectral sequence"]
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.existsFirst

/- Example 15.62.1 (2), tag `061Z`: the second spectral sequence has page one
`Tor_j^R(K_i,M)`, with differential induced by `K_i ⟶ K_(i-1)`. -/
@[stacks 061Z "(2) terms-first Tor spectral sequence"]
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.existsSecond

/- The paired existence statement and source predicates. -/
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.existsPair
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.IsFirst
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.IsSecond
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.IsBoundedBelow
