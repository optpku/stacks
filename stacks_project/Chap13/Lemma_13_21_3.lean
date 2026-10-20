/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AssociatedDerivedPages
import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.FilteredDerivedTotal
import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.AbutmentFunctor
import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.DerivedPageFunctor
import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.SpectralSequence
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.21.3

The reusable statement is split across the neutral Cartan--Eilenberg and double-complex APIs:
existence of the two associated spectral sequences, their initial-page identifications,
boundedness, finite abutment filtrations, convergence, and the two filtered-total comparisons.
-/

/- Lemma 13.21.3 (1): the two standard filtrations of the image of a Cartan--Eilenberg
resolution jointly admit associated cohomological spectral sequences. -/
@[stacks 015J] #check
  @HomologicalComplex₂.Filtration.SpectralSequence.existsPair

/- Lemma 13.21.3 (2): the first spectral sequence has
`E₁^{p,q} ≅ (F.rightDerived q).obj (K.obj.X p)`. -/
@[stacks 015J] #check
  @CochainComplex.CartanEilenbergResolution.First.Association.pageOneIso

/- Lemma 13.21.3 (3): the second spectral sequence has
`E₂^{p,q} ≅ (F.rightDerived p).obj (K.obj.homology q)`. -/
@[stacks 015J] #check
  @CochainComplex.CartanEilenbergResolution.Second.Association.pageTwoIso

/- Lemma 13.21.3 (4): the first associated spectral sequence is bounded. -/
@[stacks 015J] #check
  @CochainComplex.CartanEilenbergResolution.SpectralSequence.First.associated_isBounded

/- Lemma 13.21.3 (5): the second associated spectral sequence is bounded. -/
@[stacks 015J] #check
  @CochainComplex.CartanEilenbergResolution.SpectralSequence.Second.associated_isBounded

/- Lemma 13.21.3 (6): the first induced filtration on total cohomology is finite. -/
@[stacks 015J] #check
  @CochainComplex.CartanEilenbergResolution.SpectralSequence.First.Cohomology.isFinite

/- Lemma 13.21.3 (7): the second induced filtration on total cohomology is finite. -/
@[stacks 015J] #check
  @CochainComplex.CartanEilenbergResolution.SpectralSequence.Second.Cohomology.isFinite

/- Lemma 13.21.3 (8): the first spectral sequence converges to total cohomology. -/
@[stacks 015J] #check
  @CochainComplex.CartanEilenbergResolution.SpectralSequence.First.converges

/- Lemma 13.21.3 (9): the second spectral sequence converges to total cohomology. -/
@[stacks 015J] #check
  @CochainComplex.CartanEilenbergResolution.SpectralSequence.Second.converges

/- Lemma 13.21.3 (10): the first filtered total computes the cohomology of the bounded-below
total right-derived value. -/
@[stacks 015J] #check
  @CochainComplex.CartanEilenbergResolution.First.filteredTotalHomologyIso

/- Lemma 13.21.3 (11): the second filtered total computes the cohomology of the same
bounded-below total right-derived value. -/
@[stacks 015J] #check
  @CochainComplex.CartanEilenbergResolution.Second.filteredTotalHomologyIso

/- The neutral functorial companions package the page and abutment comparisons for later use;
they strengthen the reusable API without changing the source statement. -/
#check @CochainComplex.CartanEilenbergResolution.Bundled.First.Derived.pageOneIso
#check @CochainComplex.CartanEilenbergResolution.Bundled.First.Derived.pageTwoIso
#check @CochainComplex.CartanEilenbergResolution.Bundled.First.Derived.complex_map
#check @CochainComplex.CartanEilenbergResolution.Bundled.First.Derived.homology_map
#check @CochainComplex.CartanEilenbergResolution.Bundled.Second.Derived.pageTwoIso
#check @CochainComplex.CartanEilenbergResolution.Bundled.Second.Derived.homology_map
#check @CochainComplex.CartanEilenbergResolution.Bundled.mappedTotalHomology_map
#check @CochainComplex.CartanEilenbergResolution.Bundled.mappedTotalHomologyIso
#check @CochainComplex.CartanEilenbergResolution.Bundled.First.filteredTotalHomologyIso
#check @CochainComplex.CartanEilenbergResolution.Bundled.Second.filteredTotalHomologyIso
