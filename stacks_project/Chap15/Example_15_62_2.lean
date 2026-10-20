/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence.ChangeOfRings
import StacksCheckRecall

/-!
# Change-of-rings Tor spectral sequence

This chapter file recalls the canonical change-of-rings Tor spectral-sequence API from `ReasLib`.

@stack 068F
-/

@[expose] public section

/- Example 15.62.2, tag `068F`: for `R ⟶ S`, an `R`-module `M`, and an `S`-module `N`,
`Tor_n^S(Tor_m^R(M,S),N)` converges to `Tor_(m+n)^R(M,N)`. -/
@[stacks 068F]
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.ChangeOfRings.existsChangeOfRings

/- The canonical source predicate and its page-two and convergence projections. -/
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.ChangeOfRings.IsChangeOfRings
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.ChangeOfRings.IsChangeOfRings.pageTwoIso
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.ChangeOfRings.IsChangeOfRings.converges
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.ChangeOfRings.pageTwo
#check @CategoryTheory.DerivedCategory.TorSpectralSequence.ChangeOfRings.abutment
