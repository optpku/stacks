/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

universe u v w

open IntermediateField

namespace IntermediateField.normalClosure

variable {F : Type u} {E : Type v} {K : Type w}
variable [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]

/-- The normal closure of a separable extension in a normal ambient extension is Galois. -/
theorem isGalois_of_isSeparable [Algebra.IsSeparable F E] [Normal F K] :
    IsGalois F (IntermediateField.normalClosure F E K) := by
  rw [isGalois_iff]
  refine ⟨?_, inferInstance⟩
  rw [← le_separableClosure_iff, normalClosure_def]
  apply iSup_le
  intro f
  rw [le_separableClosure_iff]
  exact Algebra.IsSeparable.of_algHom F E
    ((AlgEquiv.ofInjectiveField f).symm.toAlgHom.comp
      (Subalgebra.equivOfEq f.range f.fieldRange.toSubalgebra
        (by ext; simp [AlgHom.mem_range])).symm.toAlgHom)

end IntermediateField.normalClosure
