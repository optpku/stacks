module

import Mathlib.CategoryTheory.Category.Preorder
import StacksCheckRecall

@[expose] public section


universe u v w

namespace CategoryTheory

variable {I : Type u} [Preorder I]
variable {C : Type v} [Category.{w} C]

/- Mathlib's `CategoryTheory.Functor` is the exact owner for both source clauses: its `obj`,
`map`, `map_id`, and `map_comp` fields are precisely the stage objects, transition morphisms,
identity law, and composition law. The direct-system index is the thin category on `I`; for an
inverse system, `Iᵒᵈ` reverses the inequalities while retaining source indices as terms of `I`.
`CategoryTheory.orderDualEquivalence` supplies the bridge to `Iᵒᵖ` when a downstream limit API
uses opposite-category indexing. Thus no local alias is needed, and both systems inherit the
standard functor and diagram APIs directly. -/

/- Definition 4.21.2 (1): a system over a preordered set `I` in a category `C` is exactly a
functor `I ⥤ C`, where `I` is viewed as the thin category attached to the preorder. The primitive
data are the stage objects `F.obj i` and transition morphisms `F.map (homOfLE hij)`, while the
compatibilities are derived from the functor laws. -/
@[stacks 0030 "systems as functors from a preorder category"]
#check (I ⥤ C)

/- Definition 4.21.2 (2): an inverse system over a preordered set `I` in a category `C` is
exactly a functor `Iᵒᵈ ⥤ C`. This keeps the source indices on the original preorder while
reversing the transition direction without extra `op`/`unop` bookkeeping. The equivalent
contravariant presentation `Iᵒᵖ ⥤ C` is a bridge view for opposite-category limit APIs, not a
second owner. -/
@[stacks 0030 "inverse systems as functors from the order-dual preorder category"]
#check (Iᵒᵈ ⥤ C)

end CategoryTheory
