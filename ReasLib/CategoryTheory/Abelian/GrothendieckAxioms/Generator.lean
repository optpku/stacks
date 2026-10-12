/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import ReasLib.CategoryTheory.Generator.Subobject
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generator characterizations of Grothendieck abelian categories

At any universe where the category is locally small and has filtered colimits, Mathlib's
equivalence-invariant Grothendieck owner is equivalent to size-indexed `AB5` plus a separator.
The source-facing proper-subobject formulation is exposed as a separate companion.
-/

@[expose] public section

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

namespace IsGrothendieckAbelian

variable (C : Type u) [Category.{v} C] [Abelian C]
  [LocallySmall.{w} C] [HasFilteredColimitsOfSize.{w, w} C]

/-- A category is Grothendieck abelian at universe `w` exactly when its `w`-small filtered
colimits are exact and it has a separator. -/
@[stacks 079B "size-indexed AB5 and separator characterization"]
theorem iff_ab5OfSize_and_hasSeparator :
    IsGrothendieckAbelian.{w} C ↔ AB5OfSize.{w, w} C ∧ HasSeparator C := sorry

/-- Definition 19.10.1: the size-indexed Grothendieck condition is equivalent to exact filtered
colimits together with an object that misses every proper subobject. -/
@[stacks 079B "size-indexed AB5 and generator characterization"]
theorem iff_ab5OfSize_and_exists_generator :
    IsGrothendieckAbelian.{w} C ↔
      AB5OfSize.{w, w} C ∧
        ∃ G : C, ∀ ⦃X : C⦄ (S : Subobject X), S ≠ ⊤ →
          ∃ f : G ⟶ X, ¬ S.Factors f := sorry

end IsGrothendieckAbelian
end CategoryTheory
