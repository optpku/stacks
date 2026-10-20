/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃ w

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A continuous functor whose sheaf pullback preserves finite limits is an exact morphism of
sites.
-/
class IsExactMorphismOfSites (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P] : Prop
    extends u.IsContinuous J K where
  /-- The sheaf pullback preserves finite limits. -/
  [preservesFiniteLimits_sheafPullback :
    PreservesFiniteLimits (u.sheafPullback (Type w) J K)]

/-- A continuous functor with finite-limit-preserving sheaf pullback is an exact morphism of sites.
-/
instance IsExactMorphismOfSites.mk' (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [u.IsContinuous J K] [PreservesFiniteLimits (u.sheafPullback (Type w) J K)] :
    IsExactMorphismOfSites J K u where

/-- A representably flat morphism of sites is exact when the sheafification and left Kan
extensions used by sheaf pullback preserve finite limits. -/
instance IsExactMorphismOfSites.of_isMorphismOfSites
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
    [HasWeakSheafify K (Type w)] [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [HasSheafify J (Type w)] [HasSheafify K (Type w)]
    [PreservesFiniteLimits (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w)]
    [IsMorphismOfSites J K u] :
    IsExactMorphismOfSites J K u := sorry

/-- The identity functor on a Grothendieck site is an exact morphism of sites. -/
instance IsExactMorphismOfSites.id (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, (𝟭 C).op.HasLeftKanExtension P] :
    IsExactMorphismOfSites J J (𝟭 C) := sorry

/-- A functor of Grothendieck sites is exact precisely when it is continuous and its sheaf pullback
preserves finite limits. -/
theorem isExactMorphismOfSites_iff (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P] [u.IsContinuous J K] :
    IsExactMorphismOfSites J K u ↔
      u.IsContinuous J K ∧ PreservesFiniteLimits (u.sheafPullback (Type w) J K) := sorry

/-- The sheaf inverse image of an exact morphism of sites is an exact functor. -/
theorem IsExactMorphismOfSites.sheafPullback_exact
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {u : C ⥤ D}
    [HasWeakSheafify K (Type w)] [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [IsExactMorphismOfSites J K u] :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w))
      (u.sheafPullback (Type w) J K) := sorry

/-- The composite of exact morphisms of sites is exact, with the middle topology supplied
explicitly. -/
theorem IsExactMorphismOfSites.comp {E : Type u₃} [Category.{v₃} E]
    {J : GrothendieckTopology C} (K : GrothendieckTopology D) {L : GrothendieckTopology E}
    (u : C ⥤ D) (v : D ⥤ E) [HasWeakSheafify K (Type w)] [HasWeakSheafify L (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [∀ Q : Dᵒᵖ ⥤ Type w, v.op.HasLeftKanExtension Q]
    [∀ P : Cᵒᵖ ⥤ Type w, (u ⋙ v).op.HasLeftKanExtension P]
    [IsExactMorphismOfSites J K u] [IsExactMorphismOfSites K L v] :
    IsExactMorphismOfSites J L (u ⋙ v) := sorry

end CategoryTheory
