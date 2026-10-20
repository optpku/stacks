module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic

/-!
# Equalizers of formal coproducts

Formal coproducts inherit equalizers by retaining the components on which the
two target-index maps agree and equalizing their component morphisms.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- Formal coproducts inherit equalizers from their component category. -/
instance instHasEqualizers [HasEqualizers C] :
    HasEqualizers (FormalCoproduct.{w} C) := sorry

end FormalCoproduct
end Limits

end CategoryTheory
