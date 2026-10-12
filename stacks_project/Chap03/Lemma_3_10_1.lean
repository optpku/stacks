/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Action.SmallBoundClosed

@[expose] public section

universe u

open CategoryTheory

/- Lemma 3.10.1. A family `S0` of `G`-sets is contained in a small object property `P`
containing the left-regular action, closed up to isomorphism under the bound
`T.size ≤ Action.bound S.size`, and admitting countable limits and colimits that agree
with the ambient action category through the canonical comparison isomorphisms.
The limit-ordinal subcategory `G-Sets_α` is represented by this small object property. -/
@[stacks 000U] #check (Action.exists_isSmallBoundClosed :
  ∀ {G : Type u} [Group G] {ι : Type u} (S0 : ι → Action (Type u) G),
    ∃ P : ObjectProperty (Action (Type u) G),
      Action.IsSmallBoundClosed P ∧ ObjectProperty.ofObj S0 ≤ P)
