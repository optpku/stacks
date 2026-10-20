/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.Splitting.Criterion
public import ReasLib.Algebra.CentralSimple.Centralizer.MaximalCommutative

/-! # Maximal Subfields Split Central Simple Algebras

A maximal subfield of a finite central division algebra splits the associated
central simple algebra.

## Main declarations

- `IsMaximalSubfield.isSplitBy` — a maximal subfield splits the ambient CSA

## References

- [Stacks Project, Tag 0750](https://stacks.math.columbia.edu/tag/0750)
-/

@[expose] public section

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [DivisionRing A] [Algebra k A] [FiniteDimensional k A]
  [Algebra.IsCentral k A]

/-- If `K₀` is a maximal `k`-subfield of a finite central skew field `A`, then
`K₀` splits the associated finite central simple `k`-algebra. -/
@[stacks 0750]
theorem IsMaximalSubfield.isSplitBy
    (K₀ : Subalgebra k A) [IsMaximalSubfield K₀] :
    (CSA.mk (AlgCat.of k A)).IsSplitBy K₀ := by
  refine (CSA.mk (AlgCat.of k A)).isSplitBy_of_self_embedding_finrank_sq K₀ ?_ ?_
  · exact ⟨K₀.val⟩
  · simpa using IsMaximalSubfield.finrank_sq K₀

end

end
