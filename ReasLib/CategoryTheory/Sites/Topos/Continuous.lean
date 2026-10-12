/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Topos morphisms from continuous functors of sites

A continuous functor of sites presents a morphism of topoi once its sheaf
pullback is known to preserve finite limits. This leaf records that construction
without imposing representable flatness, which belongs to the stronger
`IsMorphismOfSites` interface.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- The value at `X` of continuous sheaf pushforward is the value of the original sheaf at
`u.obj X`. -/
@[stacks 06NW "objectwise continuous sheaf pushforward"]
noncomputable def sheafPushforwardContinuousObjObjIso
    (u : C ⥤ D) (A : Type (w + 1)) [Category.{w} A]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [u.IsContinuous J K] (F : Sheaf K A) (X : C) :
    (((u.sheafPushforwardContinuous A J K).obj F).obj.obj (op X)) ≅
      F.obj.obj (op (u.obj X)) :=
  ((u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).app F).app (op X)

/-- The morphism of topoi presented by a continuous functor whose sheaf pullback is left exact. -/
noncomputable def morphismOfTopoiInOfContinuous
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K]
    [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (u.sheafPullback (Type w) J K)] :
    MorphismOfTopoiIn J K where
  inverseImageFunctor := LeftExactFunctor.of (u.sheafPullback (Type w) J K)
  pushforward := u.sheafPushforwardContinuous (Type w) J K
  adjunction := u.sheafAdjunctionContinuous (Type w) J K

/-- The direct image of `morphismOfTopoiInOfContinuous` is continuous sheaf pushforward. -/
@[simp]
theorem morphismOfTopoiInOfContinuous_pushforward
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K]
    [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (u.sheafPullback (Type w) J K)] :
    (u.morphismOfTopoiInOfContinuous J K).pushforward =
      u.sheafPushforwardContinuous (Type w) J K := sorry

/-- The inverse image of `morphismOfTopoiInOfContinuous` is sheaf pullback. -/
@[simp]
theorem morphismOfTopoiInOfContinuous_inverseImage
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K]
    [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (u.sheafPullback (Type w) J K)] :
    (u.morphismOfTopoiInOfContinuous J K).inverseImage =
      u.sheafPullback (Type w) J K := sorry

end CategoryTheory.Functor
