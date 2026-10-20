module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Functor.LeftKanExtension.FiniteConnectedLimits

/-!
# Finite connected limits of sheaf pullback

This leaf transfers the general left-Kan-extension criterion to pullback of
type-valued sheaves along a continuous functor of sites.
-/

@[expose] public section

open CategoryTheory Limits

universe w t v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.SheafPullback

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) [u.IsContinuous J K]
variable [HasSheafify K (Type t)]
variable [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasPointwiseLeftKanExtension P]

/-- Sheaf pullback along a continuous functor preserving finite connected limits preserves all
finite connected limits of `Type`-valued sheaves. Preservation of a particular shape is supplied
by the generic `PreservesFiniteConnectedLimits` projection. -/
instance preservesFiniteConnectedLimits
    [HasFiniteConnectedLimits C] [PreservesFiniteConnectedLimits u] :
    PreservesFiniteConnectedLimits (u.sheafPullback (Type t) J K) := sorry

namespace Pullbacks

/-- Sheaf pullback along a continuous functor that preserves pullbacks and equalizers preserves
all finite connected limits of `Type`-valued sheaves. -/
@[stacks 00XS]
theorem ofEqualizers
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    PreservesFiniteConnectedLimits (u.sheafPullback (Type t) J K) := sorry

/-- The pullback/equalizer criterion projected to an arbitrary finite connected shape. -/
theorem preservesLimitsOfShape
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (u.sheafPullback (Type t) J K) := sorry

/-- The pullback/equalizer criterion specialized to preservation of pullbacks. -/
theorem preservesPullbacks
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    PreservesLimitsOfShape WalkingCospan (u.sheafPullback (Type t) J K) := sorry

/-- The pullback/equalizer criterion specialized to preservation of equalizers. -/
theorem preservesEqualizers
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    PreservesLimitsOfShape WalkingParallelPair (u.sheafPullback (Type t) J K) := sorry

end Pullbacks

end CategoryTheory.Functor.SheafPullback
