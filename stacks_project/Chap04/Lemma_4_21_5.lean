/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.Presentable.Directed
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open Limits

universe w vA uA vC uC

variable (J : Type w) [SmallCategory J] [IsFiltered J]

/-
Mathlib's Deligne-style theorem `IsFiltered.exists_directed` is the exact structural owner: for a
small filtered category `J`, it returns one nonempty directed partial order `α` and one final
functor `F : α ⥤ J`. The source's two diagram families are then the same construction and its
opposite:

- For direct systems, start with the directed order `α`, pass to `J` through the final functor
  `F`, and then evaluate the original diagram: `α ⥤ J ⥤ C`.
- For inverse systems, take opposites. The resulting presentation is
  `αᵒᵖ ⥤ Jᵒᵖ ⥤ C`, with first map `F.op` and second map `M`.

`Functor.initial_op_of_final` supplies the second row from the first. The generic final/initial
functor API
then preserves exactly the source's one-way existence hypotheses and identifies its specified
comparison morphisms `colimit.pre` and `limit.pre` as isomorphisms. A new package quantifying over
all `C` and `M` would merely hide this reusable universal interface. The stronger
`hasColimit_comp_iff`/`colimitIso` and dual APIs remain available, but the recalls below retain the
source's stated direction and named comparison maps.
-/

/- Lemma 4.21.5 (1): every small filtered category admits a final functor from a nonempty
directed partially ordered set. -/
@[stacks 0032 "directed-poset presentation of a filtered category"]
#check (IsFiltered.exists_directed J :
  ∃ (alpha : Type w) (_ : PartialOrder alpha) (_ : IsDirected alpha (· ≤ ·))
    (_ : Nonempty alpha) (F : alpha ⥤ J), F.Final)

variable {A : Type uA} [Category.{vA} A]
variable {C : Type uC} [Category.{vC} C]
variable (F : A ⥤ J) [F.Final]
variable (M : J ⥤ C) (N : Jᵒᵖ ⥤ C)

section

variable [HasColimit (F ⋙ M)]

/- Lemma 4.21.5 (2): a colimit of the system obtained by precomposition with a final functor
induces a colimit of the original diagram. -/
@[stacks 0032 "colimit existence from the directed final system"]
#check (Functor.Final.hasColimit_of_comp F : HasColimit M)

end

section

variable [HasColimit M]

/- Lemma 4.21.5 (3): the canonical comparison `colimit.pre M F` associated to a final functor is
an isomorphism. -/
@[stacks 0032 "canonical colimit comparison for the directed final system"]
#check (Functor.Final.colimit_pre_isIso (F := F) (G := M) : IsIso (colimit.pre M F))

end

/- The opposite of a final functor is initial, which specializes the same chosen `F` to the inverse
system half of the source. -/
#check Functor.initial_op_of_final

section

variable [HasLimit (F.op ⋙ N)]

/- Lemma 4.21.5 (4): a limit of the inverse system obtained by precomposition with the initial
opposite of a final functor induces a limit of the original diagram. -/
@[stacks 0032 "limit existence from the directed inverse system"]
#check (Functor.Initial.hasLimit_of_comp F.op : HasLimit N)

end

section

variable [HasLimit N]

/- Lemma 4.21.5 (5): the canonical comparison `limit.pre M F.op` associated to the initial
opposite of a final functor is an isomorphism. -/
@[stacks 0032 "canonical limit comparison for the directed inverse system"]
#check (Functor.Initial.limit_pre_isIso (F := F.op) (G := N) : IsIso (limit.pre N F.op))

end

end CategoryTheory
