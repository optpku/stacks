/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Final
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe vI uI vJ uJ vC uC

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable (H : I ⥤ J) [H.Initial] (M : J ⥤ C)

/- The source needs both existence from either side and the resulting displayed object
isomorphism. `Functor.Initial.hasLimit_comp_iff` is the exact existence owner, while
`Functor.Initial.limitIso` is the exact comparison owner; `Functor.Initial.hasLimit_of_comp` gives
only one direction and `Functor.Initial.limit_pre_isIso` exposes the underlying comparison
morphism rather than the displayed isomorphism. The two canonical recalls separate the existence
condition from its data-level conclusion without generalizing beyond one initial functor and one
diagram, and expose both standard APIs for downstream use. -/

/- Lemma 4.17.4 (existence): for an initial functor `H : I ⥤ J` and a diagram `M : J ⥤ C`,
`H ⋙ M` has a limit if and only if `M` has a limit. -/
@[stacks 002R "limit existence is invariant under an initial functor"]
#check (CategoryTheory.Functor.Initial.hasLimit_comp_iff H :
  HasLimit (H ⋙ M) ↔ HasLimit M)

section

variable [HasLimit M]

/- Lemma 4.17.4 (canonical comparison): if a limit exists, the canonical comparison identifies
`limit (H ⋙ M)` with `limit M`. -/
@[stacks 002R "canonical limit comparison isomorphism along an initial functor"]
#check (CategoryTheory.Functor.Initial.limitIso H M : limit (H ⋙ M) ≅ limit M)

end
