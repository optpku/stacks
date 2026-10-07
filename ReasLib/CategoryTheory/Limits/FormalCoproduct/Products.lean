module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Over

/-!
# Binary products of formal coproducts

Formal coproducts inherit binary products componentwise.  The instance in this leaf is useful
for semi-representable-family constructions without tying it to a site topology.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- Formal coproducts inherit binary products from their component category. -/
instance instHasBinaryProducts [HasBinaryProducts C] :
    HasBinaryProducts (FormalCoproduct.{w} C) := sorry

end FormalCoproduct
end Limits

end CategoryTheory
