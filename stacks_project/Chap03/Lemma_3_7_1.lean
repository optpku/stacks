module

public import ReasLib.CategoryTheory.Limits.Types.Cofinality
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Cardinal
open scoped Cardinal

namespace CategoryTheory.Limits.Types

/- Lemma 3.7.1. A map into an ordinal-indexed colimit of sets factors through one stage
when its domain has cardinality less than the ordinal's cofinality. -/
@[stacks 05N2] #check (CategoryTheory.Limits.Types.exists_lift_of_lt_cof :
  ∀ {β : Ordinal.{u}} {F : β.ToType ⥤ Type u} {c : Cocone F}
    (hc : IsColimit c) {S : Type u} (φ : S ⟶ c.pt) (hS : #S < β.cof),
    ∃ (α : β.ToType) (φα : S ⟶ F.obj α), φα ≫ c.ι.app α = φ)

end CategoryTheory.Limits.Types
