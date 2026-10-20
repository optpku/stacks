/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Action.Size
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Countable
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Cardinal

namespace Action

/-- A small object property of `G`-sets containing the left-regular object and, up to
isomorphism, every `G`-set of size at most `bound (size S)` for each member `S`. Its full
subcategory has countable limits and colimits whose canonical comparisons with the ambient
category are isomorphisms. -/
structure IsSmallBoundClosed.{u} {G : Type u} [Group G]
    (P : ObjectProperty (Action (Type u) G)) : Prop where
  /-- The objects satisfying `P` form a `u`-small set. -/
  small : ObjectProperty.Small.{u} P
  /-- The left-regular `G`-set lies in `P`. -/
  contains_leftRegular : P (leftRegular G)
  /-- If `P S` and `T.size ≤ bound S.size`, then `T` is isomorphic to a member of `P`. -/
  isoClosure_of_size_le_bound {S T : Action (Type u) G} :
    P S → T.size ≤ bound S.size → P.isoClosure T
  /-- Every countable diagram in the full subcategory has a limit. -/
  hasLimit {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) : HasLimit F
  /-- The canonical comparison of countable limits is an isomorphism when both limits exist. -/
  isIso_limit_post {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) [HasLimit F] [HasLimit (F ⋙ P.ι)] :
    IsIso (limit.post F P.ι)
  /-- Every countable diagram in the full subcategory has a colimit. -/
  hasColimit {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) : HasColimit F
  /-- The canonical comparison of countable colimits is an isomorphism when both exist. -/
  isIso_colimit_post {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) [HasColimit F] [HasColimit (F ⋙ P.ι)] :
    IsIso (colimit.post F P.ι)

/-- An object property is small bound-closed when it is small, contains the left-regular
action, is closed up to isomorphism under the cardinal bound, and has countable limits and
colimits whose canonical ambient comparison morphisms are isomorphisms. -/
def isSmallBoundClosed {G : Type u} [Group G]
    {P : ObjectProperty (Action (Type u) G)}
    (small : ObjectProperty.Small.{u} P)
    (contains_leftRegular : P (leftRegular G))
    (isoClosure_of_size_le_bound : ∀ {S T : Action (Type u) G},
      P S → T.size ≤ bound S.size → P.isoClosure T)
    (hasLimit : ∀ {J : Type} [SmallCategory J] [CountableCategory J],
      (F : J ⥤ P.FullSubcategory) → HasLimit F)
    (isIso_limit_post : ∀ {J : Type} [SmallCategory J] [CountableCategory J]
      (F : J ⥤ P.FullSubcategory) [HasLimit F] [HasLimit (F ⋙ P.ι)],
      IsIso (limit.post F P.ι))
    (hasColimit : ∀ {J : Type} [SmallCategory J] [CountableCategory J],
      (F : J ⥤ P.FullSubcategory) → HasColimit F)
    (isIso_colimit_post : ∀ {J : Type} [SmallCategory J] [CountableCategory J]
      (F : J ⥤ P.FullSubcategory) [HasColimit F] [HasColimit (F ⋙ P.ι)],
      IsIso (colimit.post F P.ι)) :
    IsSmallBoundClosed P :=
  { small
    contains_leftRegular
    isoClosure_of_size_le_bound
    hasLimit
    isIso_limit_post
    hasColimit
    isIso_colimit_post }

universe u

variable {G : Type u} [Group G]

/-- A `G`-set of size at most `bound (size S)` for a member `S` of a small bound-closed
property is isomorphic to a member of that property. -/
theorem exists_iso_of_size_le_bound {P : ObjectProperty (Action (Type u) G)}
    (h : IsSmallBoundClosed P) {S T : Action (Type u) G} (hS : P S)
    (hT : T.size ≤ bound S.size) :
    ∃ S' : Action (Type u) G, P S' ∧ Nonempty (T ≅ S') := sorry

/-- `G`-sets of size at most `bound (size S)` lie in the isomorphism closure of `P`. -/
theorem sizeLE_bound_le_isoClosure {P : ObjectProperty (Action (Type u) G)}
    (h : IsSmallBoundClosed P) {S : Action (Type u) G} (hS : P S) :
    sizeLE (bound S.size) ≤ P.isoClosure := sorry

/-- Countable limits exist in the full subcategory of a small bound-closed property. -/
theorem hasLimit {P : ObjectProperty (Action (Type u) G)} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory) :
    HasLimit F := sorry

/-- The canonical comparison `limit.post F P.ι` is an isomorphism whenever both countable
limits exist for a small bound-closed property. -/
theorem isIso_limit_post {P : ObjectProperty (Action (Type u) G)} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory)
    [HasLimit F] [HasLimit (F ⋙ P.ι)] : IsIso (limit.post F P.ι) := sorry

/-- Countable colimits exist in the full subcategory of a small bound-closed property. -/
theorem hasColimit {P : ObjectProperty (Action (Type u) G)} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory) :
    HasColimit F := sorry

/-- The canonical comparison `colimit.post F P.ι` is an isomorphism whenever both countable
colimits exist for a small bound-closed property. -/
theorem isIso_colimit_post {P : ObjectProperty (Action (Type u) G)} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory)
    [HasColimit F] [HasColimit (F ⋙ P.ι)] : IsIso (colimit.post F P.ι) := sorry

/-- Every family of `G`-sets is contained in a small bound-closed object property. -/
theorem exists_isSmallBoundClosed {G : Type u} [Group G] {ι : Type u}
    (S0 : ι → Action (Type u) G) :
    ∃ P : ObjectProperty (Action (Type u) G),
      IsSmallBoundClosed P ∧ ObjectProperty.ofObj S0 ≤ P := sorry

/-- A monomorphism into a member of a small bound-closed property has domain isomorphic
to a member of that property. -/
theorem isoClosure_of_mono {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {O U : Action (Type u) G} (hU : P U) (f : O ⟶ U) [Mono f] : P.isoClosure O := sorry

/-- A stable subset of a member of a small bound-closed property is isomorphic to a
member of that property. -/
theorem isoClosure_of_stableSubset {P : ObjectProperty (Action (Type u) G)}
    (hP : IsSmallBoundClosed P) {U : Action (Type u) G} (hU : P U) (O : Set U.V)
    (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O) :
    P.isoClosure (ofStableSubset U O hO) := sorry

end Action
