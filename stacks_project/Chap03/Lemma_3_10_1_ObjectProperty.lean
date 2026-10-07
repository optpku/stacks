module

public import stacks_project.Chap03.Lemma_3_10_1_Size
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

/-- A small object property of `G`-sets which contains the left-regular object, contains up to
isomorphism every `G`-set of size at most `bound (size S)` for each member `S`, and whose
inclusion into `Action (Type u) G` creates countable limits and colimits. This is the Lean
stand-in for a Stacks category `G-Sets_α`. -/
structure IsSmallBoundClosed.{u} {G : Type u} [Group G]
    (P : ObjectProperty (Action (Type u) G)) : Prop where
  /-- The objects satisfying `P` form a `u`-small set. -/
  small : ObjectProperty.Small.{u} P
  /-- The left-regular `G`-set lies in `P`. -/
  contains_leftRegular : P (leftRegular G)
  /-- If `P S` and `T.size ≤ bound S.size`, then `T` is isomorphic to some `G`-set satisfying `P`. -/
  isoClosure_of_size_le_bound {S T : Action (Type u) G} :
    P S → T.size ≤ bound S.size → P.isoClosure T
  /-- Every countable diagram in the full subcategory has a limit. -/
  hasLimit {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) : HasLimit F
  /-- When both countable limits exist, the canonical comparison `limit.post F P.ι` is an
  isomorphism. -/
  isIso_limit_post {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) [HasLimit F] [HasLimit (F ⋙ P.ι)] :
    IsIso (limit.post F P.ι)
  /-- Every countable diagram in the full subcategory has a colimit. -/
  hasColimit {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) : HasColimit F
  /-- When both countable colimits exist, the canonical comparison `colimit.post F P.ι` is an
  isomorphism. -/
  isIso_colimit_post {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) [HasColimit F] [HasColimit (F ⋙ P.ι)] :
    IsIso (colimit.post F P.ι)

universe u

variable {G : Type u} [Group G]

/-- Clause (2) of the Stacks construction: a `G`-set of size at most `bound (size S)` is
isomorphic to some `G`-set satisfying `P`. -/
theorem exists_iso_of_size_le_bound {P : ObjectProperty (Action (Type u) G)}
    (h : IsSmallBoundClosed P) {S T : Action (Type u) G} (hS : P S)
    (hT : T.size ≤ bound S.size) :
    ∃ S' : Action (Type u) G, P S' ∧ Nonempty (T ≅ S') := sorry

/-- `G`-sets of size at most `bound (size S)` lie in the isomorphism closure of `P`. -/
theorem sizeLE_bound_le_isoClosure {P : ObjectProperty (Action (Type u) G)}
    (h : IsSmallBoundClosed P) {S : Action (Type u) G} (hS : P S) :
    sizeLE (bound S.size) ≤ P.isoClosure := sorry

/-- Countable limits exist in the full subcategory. -/
theorem hasLimit {P : ObjectProperty (Action (Type u) G)} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory) :
    HasLimit F := sorry

/-- The canonical comparison `limit.post F P.ι` is an isomorphism whenever both countable limits
exist. -/
theorem isIso_limit_post {P : ObjectProperty (Action (Type u) G)} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory)
    [HasLimit F] [HasLimit (F ⋙ P.ι)] : IsIso (limit.post F P.ι) := sorry

/-- Countable colimits exist in the full subcategory. -/
theorem hasColimit {P : ObjectProperty (Action (Type u) G)} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory) :
    HasColimit F := sorry

/-- The canonical comparison `colimit.post F P.ι` is an isomorphism whenever both countable
colimits exist. -/
theorem isIso_colimit_post {P : ObjectProperty (Action (Type u) G)} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory)
    [HasColimit F] [HasColimit (F ⋙ P.ι)] : IsIso (colimit.post F P.ι) := sorry

end Action
