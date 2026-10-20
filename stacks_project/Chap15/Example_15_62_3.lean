/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence.BaseChange
import StacksCheckRecall

/-!
# Tor spectral sequence for flat base change

This chapter file recalls the canonical Tor base-change spectral-sequence API from `ReasLib`.

@stack 0620
-/

@[expose] public section

/- Example 15.62.3, tag `0620`: if `B`, `M`, and `N` are flat over `A`, then
`Tor_i^A(Tor_j^B(M,N),A')` converges to the corresponding Tor over `B ⊗[A] A'`. -/
@[stacks 0620]
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.BaseChange.existsBaseChange

/- The canonical source predicate and its page-two and abutment projections. -/
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.BaseChange.IsBaseChange
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.BaseChange.IsBaseChange.pageTwoIso
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.BaseChange.IsBaseChange.converges
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.BaseChange.pageTwo
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.BaseChange.abutment
