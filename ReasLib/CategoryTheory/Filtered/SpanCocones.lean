/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
public import ReasLib.CategoryTheory.ConnectedComponents
public import ReasLib.CategoryTheory.Filtered.CommonSuccessors

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {I : Type u} [Category.{v} I]

/-
The source asks only for a commuting cocone on each span. The canonical concrete owner is
mathlib's `PushoutCocone`; no pushout universal property is included. The verified candidates
`IsFilteredOrEmpty`, via `IsFiltered.span`, and `HasPushouts` both imply this condition but are
strictly stronger: the former also equalizes parallel arrows, while the latter asks for universal
cocones. The `Nonempty`-valued class below therefore preserves the exact hypothesis, while
`HasSpanCocones.cocone` is the single public choice boundary for clients that need the apex and
filler maps as data.
-/
/-- A category has span cocones if every span `y ⟵ x ⟶ z` extends to a commuting square. -/
@[stacks 09WS "weak cocones on spans"]
class HasSpanCocones (I : Type u) [Category.{v} I] : Prop where
  /-- Every span admits a `PushoutCocone`, without any universal-property requirement. -/
  nonempty {x y z : I} (f : x ⟶ y) (g : x ⟶ z) :
    Nonempty (PushoutCocone f g)

namespace HasSpanCocones

/-- The selected weak pushout cocone on a span. This is the concrete-data boundary for
`HasSpanCocones`; downstream constructions can use its `pt`, `inl`, `inr`, and `condition` API. -/
@[stacks 09WS "selected weak cocone on a span"]
noncomputable def cocone [HasSpanCocones I]
    {x y z : I} (f : x ⟶ y) (g : x ⟶ z) : PushoutCocone f g :=
  Classical.choice (HasSpanCocones.nonempty f g)

/-- Construct the span-cocone property from the explicit apex-and-fillers condition. -/
theorem of
    (h : ∀ ⦃x y z : I⦄ (f : x ⟶ y) (g : x ⟶ z),
      ∃ (w : I) (fy : y ⟶ w) (gz : z ⟶ w), f ≫ fy = g ≫ gz) :
    HasSpanCocones I := sorry

end HasSpanCocones

/-- Every span in a category with span cocones has explicit commuting fillers. -/
theorem HasSpanCocones.exists [HasSpanCocones I]
    {x y z : I} (f : x ⟶ y) (g : x ⟶ z) :
    ∃ (w : I) (fy : y ⟶ w) (gz : z ⟶ w), f ≫ fy = g ≫ gz := sorry

/-- The canonical-cocone class agrees with the explicit apex-and-fillers condition. -/
@[stacks 09WS "span-cocone criterion"]
theorem hasSpanCocones_iff :
    HasSpanCocones I ↔
      ∀ ⦃x y z : I⦄ (f : x ⟶ y) (g : x ⟶ z),
        ∃ (w : I) (fy : y ⟶ w) (gz : z ⟶ w), f ≫ fy = g ≫ gz := sorry

/-
`IsFiltered.span` verifies that the stronger canonical owner `IsFilteredOrEmpty` supplies the
source condition. Keeping this one-way bridge exposes canonical filtered-category input without
claiming the absent converse.
-/
/-- A filtered-or-empty category has a commuting cocone on every span. -/
instance (priority := 100) hasSpanCocones_of_isFilteredOrEmpty
    [IsFilteredOrEmpty I] : HasSpanCocones I := sorry
/- Proof strategy: apply `IsFiltered.span` and package its apex, two legs, and commutativity
equation with `PushoutCocone.mk`; no universal property is required. -/

/-- A category with pushouts has a commuting cocone on every span. -/
instance (priority := 100) hasSpanCocones_of_hasPushouts
    [HasPushouts I] : HasSpanCocones I := sorry

/-
`CategoryTheory.decomposedEquiv` is the exact canonical disjoint-union presentation, and
`CategoryTheory.instIsConnectedComponent` supplies connectedness of every summand. Neither owner
transports the source-specific span-cocone condition, so the local inheritance theorem below is
the only additional bridge. Its scope is exactly the canonical full subcategories indexed by
`ConnectedComponents I`; it does not assert preservation by arbitrary subcategories.
-/
/- Every category is canonically equivalent to the disjoint union of its connected components. -/

namespace HasSpanCocones

/-- In a preconnected category with span cocones, any two objects admit a common successor. -/
theorem existsCommonSuccessor [HasSpanCocones I] [IsPreconnected I]
    (X Y : I) : ∃ (Z : I), Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z) := sorry
/- Proof strategy: use `IsPreconnected` to obtain a zigzag from `X` to `Y` and induct along it.
At each edge, `HasSpanCocones.cocone` combines the current common successor with the next vertex. -/

/-- A preconnected category with span cocones has common successors. -/
instance toHasCommonSuccessors
    [HasSpanCocones I] [IsPreconnected I] : HasCommonSuccessors I := sorry

end HasSpanCocones

namespace ConnectedComponents

namespace component

/-- Each canonical connected component inherits span cocones from the ambient category. -/
@[stacks 09WS "span cocones on connected components"]
instance hasSpanCocones [HasSpanCocones I]
    (j : ConnectedComponents I) : HasSpanCocones j.Component := sorry
/- Proof strategy: apply `HasSpanCocones.cocone` to the underlying ambient span. Each filler arrow
identifies the ambient apex with the original component by `ConnectedComponents.mk.eq_of_hom`,
so package the apex and fillers in the full subcategory `j.Component`. -/

end component

end ConnectedComponents

namespace HasSpanCocones

/-- Lemma 4.19.6 (Stacks 09WS): a category with span cocones is empty or is canonically a
nonempty disjoint union of connected categories that again have span cocones. The disjoint-union
equivalence is `CategoryTheory.decomposedEquiv`. -/
@[stacks 09WS "connected-component decomposition preserving span cocones"]
theorem emptyOrNonemptyComponents [HasSpanCocones I] :
    IsEmpty I ∨
      Nonempty (ConnectedComponents I) ∧
        ∀ j : ConnectedComponents I, IsConnected j.Component ∧ HasSpanCocones j.Component := sorry
/- Proof strategy: split on IsEmpty I. In the nonempty case choose an object to obtain a connected component, use instIsConnectedComponent for connectedness of each Component, and install ConnectedComponents.component.hasSpanCocones for the inherited span condition. -/

end HasSpanCocones

end CategoryTheory
