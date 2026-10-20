/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.KrullDimension.Local
public import ReasLib.RingTheory.Ideal.Quotient.PrimeSpectrum
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Dimension strata of an affine spectrum

This leaf owns the topological, ring-independent part of the dimension
stratification used by finite-type Cohen--Macaulay arguments.  Finiteness,
constructibility, and product decompositions belong to specialized leaves;
the present API only records the local-dimension fibers and their elementary
cover and bound operations.
-/

universe u

open PrimeSpectrum TopologicalSpace Topology

namespace PrimeSpectrum

variable (S : Type u) [CommRing S]

/-- The stratum of `Spec(S)` on which the local topological Krull dimension is
the natural number `d`. -/
@[stacks 00OV "local-dimension stratum"]
def dimensionStratum (d : ℕ) : Set (PrimeSpectrum S) :=
  {x | topologicalKrullDimAt x = d}

/-- Membership in a dimension stratum is the defining local-dimension equality. -/
@[simp, stacks 00OV "stratum membership"]
theorem mem_dimensionStratum (x : PrimeSpectrum S) (d : ℕ) :
    x ∈ dimensionStratum S d ↔ topologicalKrullDimAt x = d := sorry
/- Proof strategy: unfold `dimensionStratum` and close the resulting set
membership goal by `rfl`. -/

/-- Distinct natural dimension strata are disjoint. -/
@[stacks 00OV "disjoint dimension strata"]
theorem disjoint_dimensionStratum_of_ne {d e : ℕ} (hde : d ≠ e) :
    Disjoint (dimensionStratum S d) (dimensionStratum S e) := sorry
/- Proof strategy: use `Set.disjoint_left`; two membership equalities give
an equality of natural numbers after `exact_mod_cast`, contradicting `hde`. -/

/-- The natural dimension strata form a pairwise-disjoint family. -/
@[stacks 00OV "pairwise-disjoint dimension strata"]
theorem pairwiseDisjoint_dimensionStratum :
    Pairwise fun d e : ℕ ↦ Disjoint (dimensionStratum S d) (dimensionStratum S e) := sorry
/- Proof strategy: introduce distinct indices and apply
`disjoint_dimensionStratum_of_ne`. -/

/-- A point belongs to the union of natural strata exactly when its local
topological Krull dimension is a natural number. -/
@[stacks 00OV "natural-stratum union membership"]
theorem mem_iUnion_dimensionStratum_iff (x : PrimeSpectrum S) :
    x ∈ (⋃ d : ℕ, dimensionStratum S d) ↔
      ∃ d : ℕ, topologicalKrullDimAt x = d := sorry
/- Proof strategy: rewrite indexed-union membership with `Set.mem_iUnion` and
then use `mem_dimensionStratum`. -/

/-- The natural strata cover the spectrum exactly when every local dimension is
natural-valued. -/
@[stacks 00OV "natural-stratum cover criterion"]
theorem iUnion_dimensionStratum_eq_univ_iff :
    (⋃ d : ℕ, dimensionStratum S d) = Set.univ ↔
      ∀ x : PrimeSpectrum S, ∃ d : ℕ, topologicalKrullDimAt x = d := sorry
/- Proof strategy: prove the set equality pointwise and use
`mem_iUnion_dimensionStratum_iff` in both directions. -/

/-- A finite global topological-dimension bound bounds every stratum index
containing a point. -/
@[stacks 00OV "stratum index bound"]
theorem dimensionStratum_index_le_of_topologicalKrullDim_le {n d : ℕ}
    (hbound : topologicalKrullDim (PrimeSpectrum S) ≤ n)
    {x : PrimeSpectrum S} (hx : x ∈ dimensionStratum S d) :
    d ≤ n := sorry
/- Proof strategy: compare `topologicalKrullDimAt x` with the global dimension
using `topologicalKrullDimAt_le`, rewrite `hx`, and cast the resulting
`WithBot ℕ∞` inequality back to `ℕ`. -/

/-- Under a finite global bound, the set of nonempty natural strata is finite. -/
@[stacks 00OV "finite nonempty strata"]
theorem finite_nonempty_dimensionStrata_of_topologicalKrullDim_le {n : ℕ}
    (hbound : topologicalKrullDim (PrimeSpectrum S) ≤ n) :
    {d : ℕ | (dimensionStratum S d).Nonempty}.Finite := sorry
/- Proof strategy: embed the index set into `Set.Iic n` with
`dimensionStratum_index_le_of_topologicalKrullDim_le`, then use
`Set.Finite.subset`. -/

/-- If all local dimensions are natural and globally bounded by `n`, the first
`n + 1` finite strata cover the spectrum. -/
@[stacks 00OV "finite stratum cover"]
theorem iUnion_fin_dimensionStratum_eq_univ_of_topologicalKrullDim_le {n : ℕ}
    (hcover : (⋃ d : ℕ, dimensionStratum S d) = Set.univ)
    (hbound : topologicalKrullDim (PrimeSpectrum S) ≤ n) :
    (⋃ d : Fin (n + 1), dimensionStratum S (d : ℕ)) = Set.univ := sorry
/- Proof strategy: choose the natural stratum supplied by `hcover`, bound its
index with `dimensionStratum_index_le_of_topologicalKrullDim_le`, and package
it as an element of `Fin (n + 1)`. -/

end PrimeSpectrum
