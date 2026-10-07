module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Direct image of a continuous right adjoint

This module compares the continuous direct image of a right adjoint of site functors with the
cocontinuous direct image of its left adjoint. The presheaf-level comparison is exposed separately
so it can be reused by later sheaf and topos constructions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) (v : D ⥤ C)

namespace Functor.ContinuousRightAdjoint

/-- The left adjoint of a continuous site functor is cocontinuous. -/
theorem left_isCocontinuous
    (adj : u ⊣ v) [v.IsContinuous K J] :
    u.IsCocontinuous J K := sorry

/-- A continuous right adjoint defines a morphism of sites. -/
theorem right_isMorphismOfSites
    (adj : u ⊣ v) [v.IsContinuous K J] :
    IsMorphismOfSites K J v := sorry

/-- The presheaf comparison between cocontinuous direct image along `u` and restriction along
its continuous right adjoint `v`. -/
noncomputable def pushforwardPresheafIso
    (A : Type (w + 1)) [Category.{w} A]
    (adj : u ⊣ v)
    [v.IsContinuous K J]
    [u.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    u.sheafPushforwardCocontinuous A J K ⋙ sheafToPresheaf K A ≅
      sheafToPresheaf J A ⋙ (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj v.op :=
  (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J A)
      (Adjunction.rightAdjointUniq (u.op.ranAdjunction A) (adj.op.whiskerLeft A))

/-- The continuous direct image of a continuous right adjoint is canonically isomorphic to the
cocontinuous direct image of its left adjoint. -/
@[stacks 00XY]
noncomputable def pushforwardContinuousIso
    (A : Type (w + 1)) [Category.{w} A]
    (adj : u ⊣ v)
    [v.IsContinuous K J]
    [u.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    v.sheafPushforwardContinuous A K J ≅ u.sheafPushforwardCocontinuous A J K :=
  ((fullyFaithfulSheafToPresheaf K A).whiskeringRight (Sheaf J A)).preimageIso
    ((v.sheafPushforwardContinuousCompSheafToPresheafIso A K J) ≪≫
      (pushforwardPresheafIso u v A adj).symm)

end Functor.ContinuousRightAdjoint

end CategoryTheory
