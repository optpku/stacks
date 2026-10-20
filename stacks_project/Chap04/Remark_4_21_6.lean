/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.Data.Fintype.Order
public import ReasLib.CategoryTheory.Limits.WalkingIdempotent
import StacksCheckRecall

@[expose] public section

universe u v w

namespace CategoryTheory.Limits

section FiniteDirected

variable {I : Type u} [Preorder I] [Finite I] [Nonempty I] [IsDirectedOrder I]

/- Remark 4.21.6 (1): a finite directed preorder has a greatest element. This is the identity-map
specialization of `Finite.exists_le`. -/
@[stacks 09P8 "greatest element of a finite directed preorder"]
#check (Finite.exists_le (fun i : I ↦ i) : ∃ top : I, IsTop top)

end FiniteDirected

section TopStage

variable {I : Type u} [Preorder I] [OrderTop I]
variable {C : Type v} [Category.{w} C] (M : I ⥤ C)

/- Remark 4.21.6 (2): the colimit over an index with a greatest object is its value at that
object, expressed by the canonical colimit injection being an isomorphism. -/
@[stacks 09P8 "colimit identification with the greatest stage"]
#check (isIso_ι_of_isTerminal (Preorder.isTerminalTop I) M :
  IsIso (colimit.ι M (⊤ : I)))

end TopStage

/- Remark 4.21.6 (3): the walking idempotent is the one-object category of the two-element
idempotent monoid `Bool`. -/
@[stacks 09P8 "the walking-idempotent category"]
#check (WalkingIdempotent : Type)

/- Remark 4.21.6 (4): the walking-idempotent category is filtered. -/
@[stacks 09P8 "the finite filtered walking-idempotent category"]
#check (inferInstance : IsFiltered WalkingIdempotent)

variable (M : WalkingIdempotent ⥤ Type u)

/- Remark 4.21.6 (5): the image of the distinguished arrow under a walking-idempotent diagram is
idempotent. -/
@[stacks 09P8 "the diagram endomorphism attached to the idempotent arrow"]
#check (WalkingIdempotent.map_idem M :
  M.map WalkingIdempotent.idem ≫ M.map WalkingIdempotent.idem =
    M.map WalkingIdempotent.idem)

/- Remark 4.21.6 (6): the colimit of `M : WalkingIdempotent ⥤ Type u` has vertex the image of the
distinguished idempotent `M.map WalkingIdempotent.idem`. -/
@[stacks 09P8 "the walking-idempotent colimit is the idempotent image"]
#check (WalkingIdempotent.imageColimitCocone M : ColimitCocone M)

/- Remark 4.21.6 (7): the regular Bool-action diagram is a finite filtered colimit whose canonical
map from its only stage is not an isomorphism. -/
@[stacks 09P8 "a finite filtered colimit not equal to its only stage"]
#check (WalkingIdempotent.regularDiagram_colimitι_not_isIso :
  ¬ IsIso (colimit.ι WalkingIdempotent.regularDiagram WalkingIdempotent.star))

end CategoryTheory.Limits
