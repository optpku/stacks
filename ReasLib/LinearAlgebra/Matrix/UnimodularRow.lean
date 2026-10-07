module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Bezout
public import ReasLib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Unimodular rows

@stack 0ASW

A finite row is unimodular when its entries generate the unit ideal.  This
predicate is the stable interface between ideal-generation statements,
surjective linear combinations, and completion to an invertible matrix.
-/

universe u v

namespace Matrix

/-- A finite row is unimodular when its entries generate the unit ideal. -/
@[stacks 0ASW "unimodular row"]
def IsUnimodularRow {R : Type u} [CommRing R] {ι : Type v} (f : ι → R) : Prop :=
  Ideal.span (Set.range f) = ⊤

namespace IsUnimodularRow

/-- Unimodularity is equivalent to surjectivity of the associated linear-combination map. -/
@[stacks 0ASW "unimodular row linear-combination criterion"]
theorem iff_surjective_linearCombination
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] (f : ι → R) :
    IsUnimodularRow f ↔ Function.Surjective (Fintype.linearCombination R f) := sorry
-- Proof strategy: identify the range of `Fintype.linearCombination R f` with
-- `Ideal.span (Set.range f)`.  Surjectivity is equivalent to this range being
-- top, which is the definition of `IsUnimodularRow`.

/-- Every row of an invertible matrix is unimodular. -/
@[stacks 0ASW "invertible matrix rows are unimodular"]
theorem of_generalLinearGroup
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : GeneralLinearGroup ι R) (i : ι) :
    IsUnimodularRow (fun j ↦ A i j) := sorry
-- Proof strategy: use the `i`th column of `A⁻¹` as coefficients.  The
-- corresponding linear combination of the `i`th row of `A` is the `(i, i)`
-- entry of `A * A⁻¹`, hence one; apply
-- `iff_surjective_linearCombination`.

/-- Lemma 15.125.10: over a Bézout domain, a nonempty finite unimodular row is the first row of
an invertible matrix. -/
@[stacks 0ASW "Lemma 15.125.10, completion of a unimodular row"]
theorem exists_generalLinearGroup
    {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
    {n : ℕ} {f : Fin (n + 1) → R} (hf : IsUnimodularRow f) :
    ∃ A : GeneralLinearGroup (Fin (n + 1)) R, A 0 = f := sorry
-- Proof strategy: induct on `n`.  Use the Bezout property to replace the
-- initial segment of the row by a single generator, apply the induction
-- hypothesis to complete that segment, and combine the generator with the last
-- entry by a `2 × 2` Bezout matrix.  Pad and reindex this endpoint matrix, then
-- multiply the two general-linear matrices and verify the first row.

/-- The linear-combination form of completion of a unimodular row. -/
@[stacks 0ASW "unimodular row completion from linear combinations"]
theorem exists_generalLinearGroup_of_surjective
    {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
    {n : ℕ} {f : Fin (n + 1) → R}
    (hf : Function.Surjective (Fintype.linearCombination R f)) :
    ∃ A : GeneralLinearGroup (Fin (n + 1)) R, A 0 = f := sorry
-- Proof strategy: obtain `IsUnimodularRow f` from
-- `iff_surjective_linearCombination` and apply `exists_generalLinearGroup`.

end IsUnimodularRow

end Matrix
