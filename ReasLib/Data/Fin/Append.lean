module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ranges of appended finite families

This leaf records the set-level range formula for `Fin.append`, keeping finite
index arithmetic out of downstream covering and generation arguments.

@stack 00SE
-/

@[expose] public section

namespace Set

/-- The range of a family obtained by appending two finite families is the
union of their ranges. -/
@[stacks 00SE "range of an appended finite family"]
theorem range_fin_append {α : Type*} {m n : ℕ} (x : Fin m → α) (y : Fin n → α) :
    Set.range (Fin.append x y) = Set.range x ∪ Set.range y := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases ?_ ?_ i
    · intro j
      left
      exact ⟨j, (Fin.append_left x y j).symm⟩
    · intro j
      right
      exact ⟨j, (Fin.append_right x y j).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd n i, Fin.append_left x y i⟩
    · exact ⟨Fin.natAdd m j, Fin.append_right x y j⟩

end Set
