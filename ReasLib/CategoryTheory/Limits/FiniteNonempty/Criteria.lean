/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Products
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
public import Mathlib.Data.List.TFAE
import Mathlib.Tactic.CrossRefAttribute

/-!
# Criteria for finite nonempty limits and colimits

This leaf characterizes finite nonempty limits using binary products and connected-limit shapes,
and records the dual coproduct criteria.  Explicit finite nonempty product constructions live in
`FiniteNonempty.Products`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

open CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace HasFiniteNonemptyLimits

namespace BinaryProducts

/-- Binary products and finite connected limits give finite nonempty limits. -/
theorem ofFiniteConnected
    [HasBinaryProducts C] [HasFiniteConnectedLimits C] : HasFiniteNonemptyLimits C := sorry

/-- A category has finite nonempty limits if and only if it has binary products and finite
connected limits. -/
theorem iff_finiteConnected :
    HasFiniteNonemptyLimits C ↔ HasBinaryProducts C ∧ HasFiniteConnectedLimits C := sorry

/-- Binary products and equalizers give finite nonempty limits. -/
theorem ofEqualizers
    [HasBinaryProducts C] [HasEqualizers C] : HasFiniteNonemptyLimits C := sorry

/-- Binary products and pullbacks give finite nonempty limits. -/
theorem ofPullbacks
    [HasBinaryProducts C] [HasPullbacks C] : HasFiniteNonemptyLimits C := sorry

/-- A category has finite nonempty limits if and only if it has binary products and
equalizers. -/
@[stacks 04AU "finite nonempty limits versus binary products and equalizers"]
theorem iff_equalizers :
    HasFiniteNonemptyLimits C ↔ HasBinaryProducts C ∧ HasEqualizers C := sorry

/-- A category has finite nonempty limits if and only if it has binary products and
pullbacks. -/
@[stacks 04AU "finite nonempty limits versus binary products and pullbacks"]
theorem iff_pullbacks :
    HasFiniteNonemptyLimits C ↔ HasBinaryProducts C ∧ HasPullbacks C := sorry

end BinaryProducts

/-- Finite nonempty limits, binary products with equalizers, and binary products with pullbacks
are equivalent conditions. -/
@[stacks 04AU "finite nonempty limit criteria"]
theorem tfae :
    [HasFiniteNonemptyLimits C, HasBinaryProducts C ∧ HasEqualizers C,
      HasBinaryProducts C ∧ HasPullbacks C].TFAE := sorry

end HasFiniteNonemptyLimits

namespace HasFiniteNonemptyColimits

namespace BinaryCoproducts

/-- Binary coproducts and finite connected colimits give finite nonempty colimits. -/
theorem ofFiniteConnected
    [HasBinaryCoproducts C] [HasFiniteConnectedColimits C] :
    HasFiniteNonemptyColimits C := sorry

/-- A category has finite nonempty colimits if and only if it has binary coproducts and finite
connected colimits. -/
theorem iff_finiteConnected :
    HasFiniteNonemptyColimits C ↔
      HasBinaryCoproducts C ∧ HasFiniteConnectedColimits C := sorry

/-- Binary coproducts and coequalizers construct all finite nonempty colimits. -/
theorem ofCoequalizers
    [HasBinaryCoproducts C] [HasCoequalizers C] :
    HasFiniteNonemptyColimits C := sorry

/-- Binary coproducts and pushouts construct all finite nonempty colimits. -/
theorem ofPushouts
    [HasBinaryCoproducts C] [HasPushouts C] :
    HasFiniteNonemptyColimits C := sorry

/-- A category has finite nonempty colimits if and only if it has binary coproducts and
coequalizers. -/
@[stacks 04AW "finite nonempty colimits versus binary coproducts and coequalizers"]
theorem iff_coequalizers :
    HasFiniteNonemptyColimits C ↔ HasBinaryCoproducts C ∧ HasCoequalizers C := sorry

/-- A category has finite nonempty colimits if and only if it has binary coproducts and
pushouts. -/
@[stacks 04AW "finite nonempty colimits versus binary coproducts and pushouts"]
theorem iff_pushouts :
    HasFiniteNonemptyColimits C ↔ HasBinaryCoproducts C ∧ HasPushouts C := sorry

end BinaryCoproducts

/-- Finite nonempty colimits, binary coproducts with coequalizers, and binary coproducts with
pushouts are equivalent conditions. -/
@[stacks 04AW "finite nonempty colimit criteria"]
theorem tfae :
    [HasFiniteNonemptyColimits C, HasBinaryCoproducts C ∧ HasCoequalizers C,
      HasBinaryCoproducts C ∧ HasPushouts C].TFAE := sorry

end HasFiniteNonemptyColimits

end CategoryTheory.Limits
