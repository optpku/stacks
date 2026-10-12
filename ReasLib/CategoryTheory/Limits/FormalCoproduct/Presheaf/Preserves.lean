/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Preservation by formal-coproduct presheaves

The formal-coproduct presheaf construction preserves the colimits and limits
that make semi-representable families useful as a reusable presentation layer.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- The presheaf associated to a formal coproduct preserves coproducts indexed in its
formal-coproduct universe. -/
@[stacks 01G2 "(1), coproduct preservation"]
instance instToPresheafPreservesCoproductsOfShape (J : Type w) :
    PreservesColimitsOfShape (Discrete J)
      (toPresheaf : FormalCoproduct.{w} C ⥤ (Cᵒᵖ ⥤ Type (max w v))) := sorry

/-- The presheaf associated to a formal coproduct preserves every limit that exists in the
formal-coproduct category. -/
@[stacks 01G2 "(2), limit preservation"]
instance instToPresheafPreservesLimits :
    PreservesLimits
      (toPresheaf : FormalCoproduct.{w} C ⥤ (Cᵒᵖ ⥤ Type (max w v))) := sorry

end FormalCoproduct
end Limits

end CategoryTheory
