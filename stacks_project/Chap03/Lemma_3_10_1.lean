module

public import stacks_project.Chap03.Lemma_3_10_1_Size
public import stacks_project.Chap03.Lemma_3_10_1_ObjectProperty

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Cardinal

namespace Action

/-- Lemma 3.10.1. For a group `G` and a family `S0` of `G`-sets, there exists a small
object property `P` of `Action (Type u) G` containing every `S0 i` and the left-regular
`G`-set `leftRegular G`, such that whenever `P S` and `T.size ≤ bound S.size` the `G`-set
`T` is isomorphic to a member of `P`, and such that every countable diagram in
`P.FullSubcategory` has a limit and a colimit, agreeing with those in `Action (Type u) G`
via the canonical comparisons `limit.post` and `colimit.post`.

The Stacks Project packages this as a limit ordinal `α` with `G-Sets_α` the full subcategory
of `G`-sets lying in `V_α`; Lean records the same closure and comparison properties on a
small `ObjectProperty` of `Action (Type u) G`. -/
@[stacks 000U]
theorem exists_isSmallBoundClosed {G : Type u} [Group G] {ι : Type u}
    (S0 : ι → Action (Type u) G) :
    ∃ P : ObjectProperty (Action (Type u) G),
      IsSmallBoundClosed P ∧ ObjectProperty.ofObj S0 ≤ P := sorry

end Action
