/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.CategoryTheory.Sites.SheafTheoreticEmpty.Basic

/-!
# Almost cocontinuous functors of sites

This file owns the cover-lifting condition in which an arrow is allowed to
land in a sheaf-theoretically empty object.  It is a weakening of
`Functor.IsCocontinuous` that is independent of the sheafification arguments
that use it.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace Sieve

/-- The pullback of `T` along `u`, enlarged by all arrows whose image object is
sheaf-theoretically empty for `K`. -/
def almostPullback (u : C ⥤ D) (K : GrothendieckTopology D)
    {U : C} (T : Sieve (u.obj U)) : Sieve U where
  arrows := fun Y f ↦ K.IsSheafTheoreticallyEmpty (u.obj Y) ∨ (T.functorPullback u) f
  downward_closed := sorry

/-- Membership in the almost pullback is the disjunction of the
sheaf-theoretically-empty and ordinary pullback alternatives. -/
@[simp]
theorem almostPullback_apply (u : C ⥤ D) (K : GrothendieckTopology D)
    {U Y : C} (T : Sieve (u.obj U)) (f : Y ⟶ U) :
    T.almostPullback u K f ↔
      K.IsSheafTheoreticallyEmpty (u.obj Y) ∨ (T.functorPullback u) f := sorry

/-- The ordinary functor pullback sieve is contained in the almost pullback sieve. -/
theorem functorPullback_le_almostPullback (u : C ⥤ D) (K : GrothendieckTopology D)
    {U : C} (T : Sieve (u.obj U)) :
    T.functorPullback u ≤ T.almostPullback u K := sorry

end Sieve

namespace Functor

/-- A functor of sites is almost cocontinuous when each target covering sieve has a covering
almost pullback. -/
class IsAlmostCocontinuous (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) : Prop where
  almostPullback_mem {U : C} {T : Sieve (u.obj U)} (hT : T ∈ K (u.obj U)) :
      Sieve.almostPullback u K T ∈ J U

/-- Apply almost cocontinuity to a covering sieve. -/
lemma almost_cover_lift
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsAlmostCocontinuous J K] {U : C} {T : Sieve (u.obj U)}
    (hT : T ∈ K (u.obj U)) :
    Sieve.almostPullback u K T ∈ J U := sorry

/-- The covering-family formulation of almost cocontinuity: every target cover admits a source
cover whose arrows either have sheaf-theoretically empty image or factor through the target cover. -/
lemma cover_lift_factors
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsAlmostCocontinuous J K] {U : C} (T : K.Cover (u.obj U)) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      K.IsSheafTheoreticallyEmpty (u.obj I.Y) ∨
        ∃ (j : T.Arrow) (g : u.obj I.Y ⟶ j.Y), g ≫ j.f = u.map I.f := sorry

/-- Every cocontinuous functor of sites is almost cocontinuous. -/
instance isAlmostCocontinuous_of_isCocontinuous
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsCocontinuous J K] :
    IsAlmostCocontinuous u J K := sorry

end Functor

end CategoryTheory
