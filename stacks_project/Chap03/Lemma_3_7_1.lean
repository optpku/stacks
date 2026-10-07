module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Cardinal
open scoped Cardinal

namespace CategoryTheory.Limits.Types

/-- Lemma 3.7.1. If `c` is a colimit of a diagram of sets `F` indexed by ordinals less than
`β`, and `φ : S ⟶ c.pt` is a map of sets, then `φ` lifts through some stage `F.obj α` whenever
`β` is not a limit of ordinals indexed by `S`, equivalently `#S < β.cof`. -/
@[stacks 05N2]
theorem exists_lift_of_lt_cof {β : Ordinal.{u}} {F : β.ToType ⥤ Type u} {c : Cocone F}
    (hc : IsColimit c) {S : Type u} (φ : S ⟶ c.pt) (hS : #S < β.cof) :
    ∃ (α : β.ToType) (φα : S ⟶ F.obj α), φα ≫ c.ι.app α = φ := sorry

end CategoryTheory.Limits.Types
