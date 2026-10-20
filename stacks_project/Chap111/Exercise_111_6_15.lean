/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.IntegerClosedPoints
import StacksCheckRecall

@[expose] public section

/- Exercise 111.6.15 (1): the set of closed points of `Spec ℤ` is an irreducible subset. -/
@[stacks 02D8] #check (PrimeSpectrum.isIrreducible_closedPoints_int :
  IsIrreducible (closedPoints (PrimeSpectrum ℤ)))

/- Exercise 111.6.15 (2): no point of the closed points of `Spec ℤ` is a generic point of that
subset in the Stacks/subspace sense: the subset is not contained in the ambient closure of any
of its points. Contrast with Exercise 111.6.14, where every irreducible closed subset of
`Spec A` has a generic point. -/
@[stacks 02D8] #check (PrimeSpectrum.closedPoints_int_not_subset_closure_singleton :
  ∀ {x : PrimeSpectrum ℤ}, x ∈ closedPoints (PrimeSpectrum ℤ) →
    ¬ closedPoints (PrimeSpectrum ℤ) ⊆ closure {x})

/- Companion: a point of `Spec R` is closed iff its ideal is maximal. -/
#check PrimeSpectrum.isClosed_singleton_iff_isMaximal

/- Companion: `x ∈ closedPoints X` iff `IsClosed {x}`. -/
#check mem_closedPoints_iff
