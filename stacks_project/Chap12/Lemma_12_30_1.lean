/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Split
import StacksCheckRecall

/-!
# Lemma 12.30.1

Compatibility entry point for the split-(co)limit criterion. The neutral reusable API is owned by
ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Split.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uI vI uA vA

variable {I : Type uI} [Category.{vI} I]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {M : I ⥤ A}
variable (c : ColimitCocone M) (i : I)

namespace CategoryTheory

#check (EssentiallyConstant.Split.Stable.Stage c i : Prop)
#check (EssentiallyConstant.Split.Stable.HasColimit M : Prop)
#check (EssentiallyConstant.Split.Eventual.HasColimit M : Prop)
#check (EssentiallyConstant.Split.Eventual.HasLimit M : Prop)

section

variable [IsFiltered I] [IsIdempotentComplete A]

/- Lemma 12.30.1 (1)--(2): essential constancy is equivalent to the corresponding eventual
split-(co)limit criterion. -/
@[stacks 0A2E "(1)"]
#check (IsFiltered.IsEssentiallyConstant.Split.iff_eventualColimit M :
  IsFiltered.IsEssentiallyConstant M ↔ EssentiallyConstant.Split.Eventual.HasColimit M)

end

section

variable [IsCofiltered I] [IsIdempotentComplete A]

@[stacks 0A2E "(2)"]
#check (IsCofiltered.IsEssentiallyConstant.Split.iff_eventualLimit M :
  IsCofiltered.IsEssentiallyConstant M ↔ EssentiallyConstant.Split.Eventual.HasLimit M)

end

end CategoryTheory
