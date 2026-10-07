module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.IsConnected
public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer

/-!
# Finite connected limits of left Kan extensions

This leaf owns the topology-independent finite-connected-limit criterion for
left Kan extension of `Type`-valued presheaves.
-/

@[expose] public section

open CategoryTheory Limits

universe w t v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LeftKanExtension

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)
variable [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasPointwiseLeftKanExtension P]

/-- Left Kan extension along a functor preserving finite connected limits preserves all finite
connected limits of `Type`-valued presheaves. Preservation of a particular shape is supplied by
the generic `PreservesFiniteConnectedLimits` projection. -/
instance preservesFiniteConnectedLimits
    [HasFiniteConnectedLimits C] [PreservesFiniteConnectedLimits u] :
    PreservesFiniteConnectedLimits
      (u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) := sorry

namespace Pullbacks

/-- Pullback and equalizer existence and preservation give the aggregate finite-connected-limit
instance for left Kan extension. -/
theorem ofEqualizers
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    PreservesFiniteConnectedLimits
      (u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) := sorry

/-- The pullback/equalizer criterion projected to an arbitrary finite connected shape. -/
theorem preservesLimitsOfShape
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) := sorry

/-- The pullback/equalizer criterion specialized to pullbacks. -/
theorem preservesPullbacks
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    PreservesLimitsOfShape WalkingCospan
      (u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) := sorry

/-- The pullback/equalizer criterion specialized to equalizers. -/
theorem preservesEqualizers
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    PreservesLimitsOfShape WalkingParallelPair
      (u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) := sorry

end Pullbacks

end CategoryTheory.Functor.LeftKanExtension
