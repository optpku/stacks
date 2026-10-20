/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

open scoped IntermediateField
open IntermediateField
open IntermediateField.AdjoinSimple

namespace FieldExtension

section

variable {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E]

/-- Lemma 9.8.5 (Tag 09GG): a field extension is algebraic exactly when each of its simple
subextensions is finite-dimensional over the base field. -/
theorem isAlgebraicIffFiniteDimensionalAdjoinSimple :
    Algebra.IsAlgebraic k E ↔ ∀ α : E, FiniteDimensional k k⟮α⟯ := by
  constructor
  · intro h α
    exact IntermediateField.adjoin.finiteDimensional
      (isAlgebraic_iff_isIntegral.mp (h.isAlgebraic α))
  · intro h
    constructor
    intro α
    -- Local instance justification (proof-local temporary data): use the assumed finite dimensionality of the selected simple subextension to obtain its algebraicity.
    letI : FiniteDimensional k k⟮α⟯ := h α
    have hSub : Algebra.IsAlgebraic k k⟮α⟯ := Algebra.IsAlgebraic.of_finite k k⟮α⟯
    have hgen : IsAlgebraic k (AdjoinSimple.gen k α) := hSub.isAlgebraic (AdjoinSimple.gen k α)
    have hα : IsAlgebraic k ((AdjoinSimple.gen k α : k⟮α⟯) : E) :=
      (IntermediateField.isAlgebraic_iff
        (K := k) (L := E) (S := k⟮α⟯) (x := AdjoinSimple.gen k α)).mp hgen
    simpa using hα

/-- Lemma 9.8.6 (Tag 09GH): adjoining a finite family of algebraic elements to a field gives a
finite-dimensional extension. -/
theorem finiteDimensionalAdjoinRangeOfIsAlgebraic
    {K : Type v} [Field K] [Algebra k K] {ι : Type*} [Finite ι] {α : ι → K}
    (hα : ∀ i, IsAlgebraic k (α i)) :
    FiniteDimensional k (IntermediateField.adjoin k (Set.range α)) := by
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x ⟨i, rfl⟩
  exact (hα i).isIntegral

end

end FieldExtension

namespace Subring

section

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
variable [Algebra.IsAlgebraic F E]

/-- Lemma 9.8.10 (Tag 0BID): a subring of an algebraic field extension containing the base field
is itself a field. -/
theorem isFieldOfAlgebraic (R : Subring E) (hF : ∀ x : F, algebraMap F E x ∈ R) :
    IsField R := by
  let S : Subalgebra F E := Subalgebra.mk R.toSubsemiring hF
  have hS : IsField S := Subalgebra.isField_of_algebraic (A := S)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨(0 : R), (1 : R), ?_⟩
    intro hzero_one
    exact zero_ne_one (congrArg Subtype.val hzero_one)
  · intro x y
    exact Subtype.ext (mul_comm (x : E) (y : E))
  · intro a ha
    let aS : S := ⟨a, by simp [S]⟩
    have haS : aS ≠ 0 := by
      intro haS_zero
      apply ha
      simpa [aS] using congrArg Subtype.val haS_zero
    obtain ⟨bS, habS⟩ := hS.mul_inv_cancel haS
    refine ⟨⟨bS, by simp [S]⟩, ?_⟩
    apply Subtype.ext
    simpa [aS] using congrArg Subtype.val habS

end

end Subring
