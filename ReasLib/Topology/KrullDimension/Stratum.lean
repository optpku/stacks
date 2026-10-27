/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.KrullDimension.Local
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Dimension strata of a topological space

This leaf owns the topological, ring-independent part of the dimension
stratification used by finite-type Cohen--Macaulay arguments. Clopen strata,
equidimensionality, and product decompositions belong to specialized leaves;
the present API only records the local-dimension fibers and their elementary
cover and bound operations.
-/

universe u

variable (X : Type u) [TopologicalSpace X]

/-- The stratum of `X` on which the local topological Krull dimension is
the natural number `d`. -/
@[stacks 00OV "local-dimension stratum"]
def topologicalKrullDimStratum (d : ℕ) : Set X :=
  {x | topologicalKrullDimAt x = d}

/-- Membership in a dimension stratum is the defining local-dimension equality. -/
@[simp, stacks 00OV "stratum membership"]
theorem mem_topologicalKrullDimStratum (x : X) (d : ℕ) :
    x ∈ topologicalKrullDimStratum X d ↔ topologicalKrullDimAt x = d := Iff.rfl

/-- Distinct natural dimension strata are disjoint. -/
@[stacks 00OV "disjoint dimension strata"]
theorem disjoint_topologicalKrullDimStratum_of_ne {d e : ℕ} (hde : d ≠ e) :
    Disjoint (topologicalKrullDimStratum X d) (topologicalKrullDimStratum X e) := sorry
/- Proof strategy: use `Set.disjoint_left`; two membership equalities give
an equality of natural numbers after `exact_mod_cast`, contradicting `hde`. -/

/-- The natural dimension strata form a pairwise-disjoint family. -/
@[stacks 00OV "pairwise-disjoint dimension strata"]
theorem pairwiseDisjoint_topologicalKrullDimStratum :
    Pairwise fun d e : ℕ ↦
      Disjoint (topologicalKrullDimStratum X d) (topologicalKrullDimStratum X e) := sorry
/- Proof strategy: introduce distinct indices and apply
`disjoint_topologicalKrullDimStratum_of_ne`. -/

/-- A point belongs to the union of natural strata exactly when its local
topological Krull dimension is a natural number. -/
@[stacks 00OV "natural-stratum union membership"]
theorem mem_iUnion_topologicalKrullDimStratum_iff (x : X) :
    x ∈ (⋃ d : ℕ, topologicalKrullDimStratum X d) ↔
      ∃ d : ℕ, topologicalKrullDimAt x = d := sorry
/- Proof strategy: rewrite indexed-union membership with `Set.mem_iUnion` and
then use `mem_topologicalKrullDimStratum`. -/

/-- The natural strata cover the space exactly when every local dimension is
natural-valued. -/
@[stacks 00OV "natural-stratum cover criterion"]
theorem iUnion_topologicalKrullDimStratum_eq_univ_iff :
    (⋃ d : ℕ, topologicalKrullDimStratum X d) = Set.univ ↔
      ∀ x : X, ∃ d : ℕ, topologicalKrullDimAt x = d := sorry
/- Proof strategy: prove the set equality pointwise and use
`mem_iUnion_topologicalKrullDimStratum_iff` in both directions. -/

/-- A finite global topological-dimension bound bounds every stratum index
containing a point. -/
@[stacks 00OV "stratum index bound"]
theorem topologicalKrullDimStratum_index_le_of_topologicalKrullDim_le {n d : ℕ}
    (hbound : topologicalKrullDim X ≤ n)
    {x : X} (hx : x ∈ topologicalKrullDimStratum X d) :
    d ≤ n := sorry
/- Proof strategy: compare `topologicalKrullDimAt x` with the global dimension
using `topologicalKrullDimAt_le_topologicalKrullDim`, rewrite `hx`, and cast the resulting
`WithBot ℕ∞` inequality back to `ℕ`. -/

/-- Under a finite global bound, the set of nonempty natural strata is finite. -/
@[stacks 00OV "finite nonempty strata"]
theorem finite_nonempty_topologicalKrullDimStrata_of_topologicalKrullDim_le {n : ℕ}
    (hbound : topologicalKrullDim X ≤ n) :
    {d : ℕ | (topologicalKrullDimStratum X d).Nonempty}.Finite := sorry
/- Proof strategy: embed the index set into `Set.Iic n` with
`topologicalKrullDimStratum_index_le_of_topologicalKrullDim_le`, then use
`Set.Finite.subset`. -/

/-- If all local dimensions are natural and globally bounded by `n`, the first
`n + 1` finite strata cover the space. -/
@[stacks 00OV "finite stratum cover"]
theorem iUnion_fin_topologicalKrullDimStratum_eq_univ_of_topologicalKrullDim_le {n : ℕ}
    (hcover : (⋃ d : ℕ, topologicalKrullDimStratum X d) = Set.univ)
    (hbound : topologicalKrullDim X ≤ n) :
    (⋃ d : Fin (n + 1), topologicalKrullDimStratum X (d : ℕ)) = Set.univ := sorry
/- Proof strategy: choose the natural stratum supplied by `hcover`, bound its
index with `topologicalKrullDimStratum_index_le_of_topologicalKrullDim_le`, and package
it as an element of `Fin (n + 1)`. -/
