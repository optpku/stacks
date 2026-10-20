/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Criteria
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C]

/- Lemma 4.18.3 (1): a category has finite nonempty limits if and only if it has binary products
and equalizers. -/
@[stacks 04AU "finite nonempty limits versus binary products and equalizers"]
#check (HasFiniteNonemptyLimits.BinaryProducts.iff_equalizers C :
  HasFiniteNonemptyLimits C ↔ HasBinaryProducts C ∧ HasEqualizers C)

/- Lemma 4.18.3 (2): a category has finite nonempty limits if and only if it has binary products
and fibre products. -/
@[stacks 04AU "finite nonempty limits versus binary products and pullbacks"]
#check (HasFiniteNonemptyLimits.BinaryProducts.iff_pullbacks C :
  HasFiniteNonemptyLimits C ↔ HasBinaryProducts C ∧ HasPullbacks C)

/- Lemma 4.18.3: the three finite-nonempty-limit criteria form one equivalence family. -/
@[stacks 04AU "three equivalent finite nonempty limit criteria"]
#check (HasFiniteNonemptyLimits.tfae C :
  [HasFiniteNonemptyLimits C, HasBinaryProducts C ∧ HasEqualizers C,
    HasBinaryProducts C ∧ HasPullbacks C].TFAE)

end CategoryTheory.Limits
