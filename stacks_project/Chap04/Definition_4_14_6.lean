module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe v u w

variable {C : Type u} [Category.{v} C]
variable {I : Type w} (M : I → C) [HasProduct M]

/- `HasProduct M` exactly records existence of the limit of `Discrete.functor M`, while
`piObj M` is definitionally that limit and is therefore the canonical source-facing owner.
`Pi.π` and `Pi.isoLimit` are downstream projection and comparison APIs, not the definition itself.
Recalling `piObj` keeps the index type and family fully general and exposes the standard limit API
whenever `[HasProduct M]` is available. -/

/- Definition 4.14.6: for a type `I` and a family `M : I → C`, the categorical product `∏ᶜ M`
is `limit (Discrete.functor M)` when that limit exists. -/
@[stacks 002I "product as the limit of the discrete diagram of its factors"]
#check (piObj M : C)

end CategoryTheory.Limits
