/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.CategoryTheory.Filtered.Basic
import StacksCheckRecall

@[expose] public section

universe u v w

namespace CategoryTheory

variable {I : Type u} [Preorder I]
variable {C : Type v} [Category.{w} C]

/- A directed system has no structure or property beyond its indexing shape: directedness is a
condition on `I`, not on a functor `F`. Thus the canonical Lean presentation is a functor under
ambient `[Nonempty I] [IsDirectedOrder I]` instances. Introducing a predicate that accepts `F`
but ignores it would obscure this dependency and burden every downstream statement with a
spurious argument.

Mathlib turns these order-theoretic assumptions into `[IsFiltered I]`; on the order dual it gives
`[IsCofiltered Iᵒᵈ]`. These are the categorical bridges used by general (co)limit APIs, not a
second definition of directed system. This also distinguishes the present notion from
`F.IsFilteredModuloKernel` of Definition 4.19.1, whose weaker Stacks condition genuinely depends on
the action of `F` on morphisms. -/

section DirectedSystems

variable [Nonempty I] [IsDirectedOrder I]

/- Definition 4.21.4 (1): a directed system in `C` is a functor `I ⥤ C` whose indexing preorder
is nonempty and directed, as expressed by the ambient instances. -/
@[stacks 0031 "systems indexed by nonempty directed preorders"]
#check (I ⥤ C)

/- Definition 4.21.4 (2): a directed inverse system in `C` is a functor `Iᵒᵈ ⥤ C` under the same
directedness assumptions on `I`. -/
@[stacks 0031 "inverse systems indexed by nonempty directed preorders"]
#check (Iᵒᵈ ⥤ C)

/- The thin category associated to a nonempty directed preorder is canonically filtered. -/
#check (inferInstance : IsFiltered I)

/- Dually, the order-dual index of a directed inverse system is canonically cofiltered. -/
#check (inferInstance : IsCofiltered Iᵒᵈ)

end DirectedSystems

end CategoryTheory
