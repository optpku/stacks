module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Final
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Limits

/-!
# Eventual Split (Co)limits

This leaf records the split-stage criterion for essential constancy.  The criterion is independent
of a particular textbook presentation and is useful whenever a filtered diagram stabilizes up to an
eventually vanishing complementary summand.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe uI vI uA vA

namespace CategoryTheory

section Filtered

variable {I : Type uI} [Category.{vI} I]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]

namespace EssentiallyConstant.Split

namespace Stable

/-- A stage of a colimit cone has a stable split presentation when it decomposes into a summand
mapping isomorphically to the colimit and a complementary summand eventually killed by a
transition map. -/
def Stage {M : I ⥤ A} (c : ColimitCocone M) (i : I) : Prop :=
  ∃ (X Z : A) (f : X ⟶ M.obj i) (g : M.obj i ⟶ Z) (zero : f ≫ g = 0)
    (splitting : (ShortComplex.mk f g zero).Splitting),
      IsIso (f ≫ c.cocone.ι.app i) ∧
        ∃ (j : I) (hij : i ⟶ j), splitting.s ≫ M.map hij = 0

/-- A colimit is stably split when every stage has a stable split presentation. -/
def HasColimit (M : I ⥤ A) : Prop :=
  ∃ c : ColimitCocone M, ∀ i : I, Stage c i

end Stable

namespace Eventual

/-- A filtered diagram has an eventual split colimit when a cofinal filtered full subcategory has
a stably split colimit. -/
@[stacks 0A2E]
def HasColimit (M : I ⥤ A) : Prop :=
  ∃ P : ObjectProperty I,
    ∃ _ : IsFiltered P.FullSubcategory,
      ∃ _ : Functor.Final P.ι,
        Stable.HasColimit (P.ι ⋙ M)

end Eventual

end EssentiallyConstant.Split

namespace IsFiltered.IsEssentiallyConstant.Split

/-- In a filtered idempotent-complete preadditive category, essential
constancy is equivalent to the eventual split-colimit criterion. -/
@[stacks 0A2E]
theorem iff_eventualColimit
    [IsFiltered I] [IsIdempotentComplete A] (M : I ⥤ A) :
    IsFiltered.IsEssentiallyConstant M ↔ EssentiallyConstant.Split.Eventual.HasColimit M := sorry

end IsFiltered.IsEssentiallyConstant.Split

end Filtered

section Cofiltered

variable {I : Type uI} [Category.{vI} I]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]

namespace EssentiallyConstant.Split.Eventual

/-- A cofiltered diagram has an eventual split limit when its opposite has an eventual split
colimit. -/

abbrev HasLimit (M : I ⥤ A) : Prop :=
  HasColimit M.op

end EssentiallyConstant.Split.Eventual

namespace IsCofiltered.IsEssentiallyConstant.Split

/-- In a cofiltered idempotent-complete preadditive category, essential
constancy is equivalent to the eventual split-limit criterion. -/
@[stacks 0A2E]
theorem iff_eventualLimit
    [IsCofiltered I] [IsIdempotentComplete A] (M : I ⥤ A) :
    IsCofiltered.IsEssentiallyConstant M ↔ EssentiallyConstant.Split.Eventual.HasLimit M := sorry

end IsCofiltered.IsEssentiallyConstant.Split

end Cofiltered

end CategoryTheory
