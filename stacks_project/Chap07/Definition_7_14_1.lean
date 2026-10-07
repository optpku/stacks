module

public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃ w

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Definition 7.14.1: a morphism of sites `f : (D, K) ⟶ (C, J)` is given by a continuous
functor `u : C ⥤ D` such that the sheaf inverse image `u.sheafPullback` is exact. The functor
`u` goes in the opposite direction to `f`. After the definition one writes the inverse image as
`u.sheafPullback` and the direct image as `u.sheafPushforwardContinuous`, adjoint on sheaves.
Since `u.sheafPullback` is a left adjoint, exactness is equivalent to preservation of finite
limits. This is strictly weaker than `IsMorphismOfSites`, which additionally requires
representable flatness. -/
@[stacks 00X1]
class IsExactMorphismOfSites (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P] : Prop
    extends u.IsContinuous J K where
  /-- The sheaf inverse image `u.sheafPullback` preserves finite limits, i.e. is left exact. -/
  [preservesFiniteLimits_sheafPullback :
    PreservesFiniteLimits (u.sheafPullback (Type w) J K)]

/-- Constructor: a continuous functor whose sheaf pullback preserves finite limits presents a
morphism of sites in the sense of Definition 7.14.1. -/
instance IsExactMorphismOfSites.mk' (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [u.IsContinuous J K] [PreservesFiniteLimits (u.sheafPullback (Type w) J K)] :
    IsExactMorphismOfSites J K u where

/-- A representably flat morphism of sites in the sense of `IsMorphismOfSites` is an exact
morphism of sites, once sheafification of both sites and finite-limit preservation of
`u.op.lan` supply left exactness of the sheaf pullback. -/
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

/-- A functor of Grothendieck sites is an exact morphism of sites iff it is continuous and its
sheaf pullback preserves finite limits. -/
theorem isExactMorphismOfSites_iff (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P] [u.IsContinuous J K] :
    IsExactMorphismOfSites J K u ↔
      u.IsContinuous J K ∧ PreservesFiniteLimits (u.sheafPullback (Type w) J K) := sorry

/-- The sheaf inverse image along an exact morphism of sites is an exact functor. -/
theorem IsExactMorphismOfSites.sheafPullback_exact
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {u : C ⥤ D}
    [HasWeakSheafify K (Type w)] [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [IsExactMorphismOfSites J K u] :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w))
      (u.sheafPullback (Type w) J K) := sorry

/-- Composition of exact morphisms of sites, with the middle topology supplied explicitly
because it cannot be recovered from the composite functor alone. -/
theorem IsExactMorphismOfSites.comp {E : Type u₃} [Category.{v₃} E]
    {J : GrothendieckTopology C} (K : GrothendieckTopology D) {L : GrothendieckTopology E}
    (u : C ⥤ D) (v : D ⥤ E) [HasWeakSheafify K (Type w)] [HasWeakSheafify L (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [∀ Q : Dᵒᵖ ⥤ Type w, v.op.HasLeftKanExtension Q]
    [∀ P : Cᵒᵖ ⥤ Type w, (u ⋙ v).op.HasLeftKanExtension P]
    [IsExactMorphismOfSites J K u] [IsExactMorphismOfSites K L v] :
    IsExactMorphismOfSites J L (u ⋙ v) := sorry

end CategoryTheory
