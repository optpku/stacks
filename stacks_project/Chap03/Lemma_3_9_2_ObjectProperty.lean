module

public import stacks_project.Chap03.Lemma_3_9_4_Size
public import stacks_project.Chap03.«3_9_1_1_Bound»
public import stacks_project.Chap03.Lemma_3_9_1_Size
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Countable
public import Mathlib.CategoryTheory.Limits.HasLimits

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- A small object property of schemes which contains, up to isomorphism, every scheme of size
at most `bound (size S)` for each member `S`, and whose inclusion into `Scheme` compares
countable limits and colimits. This is the Lean stand-in for a Stacks category `Sch_α`. -/
structure IsSmallBoundClosed.{u} (P : ObjectProperty Scheme.{u}) : Prop where
  /-- The objects satisfying `P` form a `u`-small set. -/
  small : ObjectProperty.Small.{u} P
  /-- If `P S` and `T.size ≤ bound S.size`, then `T` is isomorphic to some scheme satisfying `P`. -/
  isoClosure_of_size_le_bound {S T : Scheme.{u}} :
    P S → T.size ≤ bound S.size → P.isoClosure T
  /-- A countable diagram in the full subcategory has a limit if and only if its composite with
  the inclusion has a limit in `Scheme`. -/
  hasLimit_iff {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) : HasLimit F ↔ HasLimit (F ⋙ P.ι)
  /-- When both countable limits exist, the canonical comparison `limit.post F P.ι` is an
  isomorphism. -/
  isIso_limit_post {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) [HasLimit F] [HasLimit (F ⋙ P.ι)] :
    IsIso (limit.post F P.ι)
  /-- A countable diagram in the full subcategory has a colimit if and only if its composite with
  the inclusion has a colimit in `Scheme`. -/
  hasColimit_iff {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) : HasColimit F ↔ HasColimit (F ⋙ P.ι)
  /-- When both countable colimits exist, the canonical comparison `colimit.post F P.ι` is an
  isomorphism. -/
  isIso_colimit_post {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ P.FullSubcategory) [HasColimit F] [HasColimit (F ⋙ P.ι)] :
    IsIso (colimit.post F P.ι)

universe u

/-- Clause (2) of the Stacks construction: a scheme of size at most `bound (size S)` is
isomorphic to some scheme satisfying `P`. -/
theorem exists_iso_of_size_le_bound {P : ObjectProperty Scheme.{u}} (h : IsSmallBoundClosed P)
    {S T : Scheme.{u}} (hS : P S) (hT : T.size ≤ bound S.size) :
    ∃ S' : Scheme.{u}, P S' ∧ Nonempty (T ≅ S') := sorry

/-- Schemes of size at most `bound (size S)` lie in the isomorphism closure of `P`. -/
theorem sizeLE_bound_le_isoClosure {P : ObjectProperty Scheme.{u}} (h : IsSmallBoundClosed P)
    {S : Scheme.{u}} (hS : P S) : sizeLE (bound S.size) ≤ P.isoClosure := sorry

/-- Countable limits in the full subcategory exist if and only if the composite diagram has a
limit in `Scheme`. -/
theorem hasLimit_iff {P : ObjectProperty Scheme.{u}} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory) :
    HasLimit F ↔ HasLimit (F ⋙ P.ι) := sorry

/-- The canonical comparison `limit.post F P.ι` is an isomorphism whenever both countable limits
exist. -/
theorem isIso_limit_post {P : ObjectProperty Scheme.{u}} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory)
    [HasLimit F] [HasLimit (F ⋙ P.ι)] : IsIso (limit.post F P.ι) := sorry

/-- Countable colimits in the full subcategory exist if and only if the composite diagram has a
colimit in `Scheme`. -/
theorem hasColimit_iff {P : ObjectProperty Scheme.{u}} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory) :
    HasColimit F ↔ HasColimit (F ⋙ P.ι) := sorry

/-- The canonical comparison `colimit.post F P.ι` is an isomorphism whenever both countable
colimits exist. -/
theorem isIso_colimit_post {P : ObjectProperty Scheme.{u}} (h : IsSmallBoundClosed P)
    {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory)
    [HasColimit F] [HasColimit (F ⋙ P.ι)] : IsIso (colimit.post F P.ι) := sorry

end AlgebraicGeometry.Scheme
