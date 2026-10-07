module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.EssentialFiniteness

@[expose] public section

/-!
# Finite generation of field extensions

Bridges between essential finite type and generation of the top intermediate field by a finite
set.
-/

universe u v

namespace IntermediateField

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- A field extension is essentially of finite type iff a finite set generates its top
intermediate field. -/
theorem essFiniteType_iff_exists_finite_adjoin_eq_top :
    Algebra.EssFiniteType k F ↔ ∃ S : Set F, S.Finite ∧ adjoin k S = ⊤ := by
  rw [← fg_top_iff, fg_def]

end IntermediateField
