/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Ind.EssentiallyConstant
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Remark 4.22.4 (1): the category of ind-objects is mathlib's canonical `Ind C`. -/
@[stacks 05PW "the category of ind-objects"]
#check (Ind C : Type (max u (v + 1)))

/- Remark 4.22.4 (2): constant systems are embedded by `Ind.yoneda`. -/
@[stacks 05PW "the constant-system embedding"]
#check (Ind.yoneda (C := C) : C ⥤ Ind C)

/- Remark 4.22.4 (3): the constant-system embedding is fully faithful. -/
@[stacks 05PW "full faithfulness of the constant-system embedding"]
#check (Ind.yoneda.fullyFaithful (C := C) : (Ind.yoneda (C := C)).FullyFaithful)

variable {C}

variable {I J : Type v} [SmallCategory I] [IsFiltered I]
variable [SmallCategory J] [IsFiltered J]
variable (M : I ⥤ C) (N : J ⥤ C)

/- Remark 4.22.4 (4): a filtered diagram determines its ind-object through `Ind.lim`. -/
@[stacks 05PW "filtered diagrams as ind-objects"]
#check (Ind.lim (C := C) I : (I ⥤ C) ⥤ Ind C)

/- Remark 4.22.4 (5): morphisms between presented ind-objects satisfy the limit-colimit formula. -/
@[stacks 05PW "the limit-colimit formula for morphisms of ind-objects"]
#check (Ind.limHomEquiv M N :
  ((Ind.lim I).obj M ⟶ (Ind.lim J).obj N) ≃
    limit (M.op ⋙ colimit (N ⋙ yoneda)))

/- Remark 4.22.4 (6): essential constancy is equivalent to being a constant ind-object. -/
@[stacks 05PW "essentially constant diagrams as constant ind-objects"]
#check (IsFiltered.isEssentiallyConstant.iff_exists_yonedaIsoLim M :
  IsFiltered.IsEssentiallyConstant M ↔
    ∃ X : C, Nonempty (Ind.yoneda.obj X ≅ (Ind.lim I).obj M))

end CategoryTheory
