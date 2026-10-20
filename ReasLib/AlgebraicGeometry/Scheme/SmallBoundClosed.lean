module

public import ReasLib.AlgebraicGeometry.Scheme.Size
public import ReasLib.SetTheory.Cardinal.Bound
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

universe u

/-- A small object property of schemes which represents every scheme of size at most
`Cardinal.countableSuccBound S.size` for each member `S`, and whose inclusion into `Scheme`
detects countable limits and colimits with isomorphic canonical comparison morphisms. -/
structure IsSmallBoundClosed (P : ObjectProperty Scheme.{u}) : Prop where
  /-- The objects satisfying `P` form a `u`-small set. -/
  small : ObjectProperty.Small.{u} P
  /-- If `P S` and `T.size ≤ Cardinal.countableSuccBound S.size`, then `T` is isomorphic to some scheme satisfying `P`. -/
  isoClosure_of_size_le_bound {S T : Scheme.{u}} :
    P S → T.size ≤ Cardinal.countableSuccBound S.size → P.isoClosure T
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

/-- An object property is small bound-closed if it is small, represents all schemes within
the cardinal bound of each member, and detects countable limits and colimits with isomorphic
canonical ambient comparison morphisms. -/
def isSmallBoundClosed {P : ObjectProperty Scheme.{u}}
    (small : ObjectProperty.Small.{u} P)
    (isoClosure_of_size_le_bound : ∀ {S T : Scheme.{u}},
      P S → T.size ≤ Cardinal.countableSuccBound S.size → P.isoClosure T)
    (hasLimit_iff : ∀ {J : Type} [SmallCategory J] [CountableCategory J]
      (F : J ⥤ P.FullSubcategory), HasLimit F ↔ HasLimit (F ⋙ P.ι))
    (isIso_limit_post : ∀ {J : Type} [SmallCategory J] [CountableCategory J]
      (F : J ⥤ P.FullSubcategory) [HasLimit F] [HasLimit (F ⋙ P.ι)],
      IsIso (limit.post F P.ι))
    (hasColimit_iff : ∀ {J : Type} [SmallCategory J] [CountableCategory J]
      (F : J ⥤ P.FullSubcategory), HasColimit F ↔ HasColimit (F ⋙ P.ι))
    (isIso_colimit_post : ∀ {J : Type} [SmallCategory J] [CountableCategory J]
      (F : J ⥤ P.FullSubcategory) [HasColimit F] [HasColimit (F ⋙ P.ι)],
      IsIso (colimit.post F P.ι)) :
    IsSmallBoundClosed P :=
  { small
    isoClosure_of_size_le_bound
    hasLimit_iff
    isIso_limit_post
    hasColimit_iff
    isIso_colimit_post }

end AlgebraicGeometry.Scheme
