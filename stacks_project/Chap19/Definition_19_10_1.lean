/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.Generator
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (A : Type u) [Category.{v} A] [Abelian A]

/- Definition 19.10.1 (1): direct sums are the canonical structure `HasCoproducts A`. -/
@[stacks 079B] #check (HasCoproducts A : Prop)

section

variable [HasCoproducts A]

/- Definition 19.10.1 (2): exact direct sums are the canonical axiom `AB4`. -/
@[stacks 079B] #check (AB4 A : Prop)

end


section

variable [HasFilteredColimits A]

/- Definition 19.10.1 (3): exact filtered colimits are the canonical axiom `AB5`. -/
@[stacks 079B] #check (AB5 A : Prop)

end

/- Definition 19.10.1 (4): products are the canonical structure `HasProducts A`. -/
@[stacks 079B] #check (HasProducts A : Prop)

section

variable [HasProducts A]

/- Definition 19.10.1 (5): exact products are the canonical axiom `AB4Star`. -/
@[stacks 079B] #check (AB4Star A : Prop)

end


section

variable [HasCofilteredLimits A]

/- Definition 19.10.1 (6): exact cofiltered limits are the canonical axiom `AB5Star`. -/
@[stacks 079B] #check (AB5Star A : Prop)

end

/- Definition 19.10.1 (7): a generator is the canonical predicate `IsSeparator`. -/
@[stacks 079B] #check (IsSeparator : A → Prop)

variable (G : A)

/- Definition 19.10.1 (7): the generator condition is equivalently detected by proper
subobjects. -/
@[stacks 079B] #check
  (isSeparator_iff_exists_not_factors_subobject A G :
    IsSeparator G ↔
      ∀ ⦃X : A⦄ (S : Subobject X), S ≠ ⊤ → ∃ f : G ⟶ X, ¬ S.Factors f)

/- Definition 19.10.1 (8): the category-level owner is `IsGrothendieckAbelian`. -/
@[stacks 079B] #check (IsGrothendieckAbelian.{v} A : Prop)

section

variable [HasFilteredColimits A]

/- Definition 19.10.1 (8): specializing the size-indexed owner to the category universe gives
the strict `AB5` plus generator characterization. -/
@[stacks 079B] #check
  (IsGrothendieckAbelian.iff_ab5OfSize_and_exists_generator.{v} A :
    IsGrothendieckAbelian.{v} A ↔
      AB5 A ∧
        ∃ G : A, ∀ ⦃X : A⦄ (S : Subobject X), S ≠ ⊤ →
          ∃ f : G ⟶ X, ¬ S.Factors f)

end

end CategoryTheory
