module

public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Preserves
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Criteria for preserving finite nonempty limits and colimits

This leaf turns the generator presentations by binary (co)products and (co)equalizers or
(co)pullbacks into direct preservation APIs. Constructor theorems assume the relevant limits only
in the source category; target existence is not part of preservation.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace PreservesFiniteNonemptyLimits.BinaryProducts

/-- Preservation of binary products and equalizers gives preservation of finite nonempty
limits. -/
theorem ofEqualizers
    (F : C ⥤ D) [HasBinaryProducts C] [HasEqualizers C]
    [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimitsOfShape WalkingParallelPair F] :
    PreservesFiniteNonemptyLimits F := sorry

/-- Preservation of binary products and pullbacks gives preservation of finite nonempty
limits. -/
theorem ofPullbacks
    (F : C ⥤ D) [HasBinaryProducts C] [HasPullbacks C]
    [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimitsOfShape WalkingCospan F] :
    PreservesFiniteNonemptyLimits F := sorry

/-- When the source has finite nonempty limits, a functor preserves them exactly when it
preserves binary products and equalizers. -/
theorem iff_equalizers
    (F : C ⥤ D) [HasFiniteNonemptyLimits C] :
    PreservesFiniteNonemptyLimits F ↔
      PreservesLimitsOfShape (Discrete WalkingPair) F ∧
        PreservesLimitsOfShape WalkingParallelPair F := sorry

/-- When the source has finite nonempty limits, a functor preserves them exactly when it
preserves binary products and pullbacks. -/
theorem iff_pullbacks
    (F : C ⥤ D) [HasFiniteNonemptyLimits C] :
    PreservesFiniteNonemptyLimits F ↔
      PreservesLimitsOfShape (Discrete WalkingPair) F ∧
        PreservesLimitsOfShape WalkingCospan F := sorry

end PreservesFiniteNonemptyLimits.BinaryProducts

namespace PreservesFiniteNonemptyColimits.BinaryCoproducts

/-- Preservation of binary coproducts and coequalizers gives preservation of finite nonempty
colimits. -/
theorem ofCoequalizers
    (F : C ⥤ D) [HasBinaryCoproducts C] [HasCoequalizers C]
    [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [PreservesColimitsOfShape WalkingParallelPair F] :
    PreservesFiniteNonemptyColimits F := sorry

/-- Preservation of binary coproducts and pushouts gives preservation of finite nonempty
colimits. -/
theorem ofPushouts
    (F : C ⥤ D) [HasBinaryCoproducts C] [HasPushouts C]
    [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [PreservesColimitsOfShape WalkingSpan F] :
    PreservesFiniteNonemptyColimits F := sorry

/-- When the source has finite nonempty colimits, a functor preserves them exactly when it
preserves binary coproducts and coequalizers. -/
theorem iff_coequalizers
    (F : C ⥤ D) [HasFiniteNonemptyColimits C] :
    PreservesFiniteNonemptyColimits F ↔
      PreservesColimitsOfShape (Discrete WalkingPair) F ∧
        PreservesColimitsOfShape WalkingParallelPair F := sorry

/-- When the source has finite nonempty colimits, a functor preserves them exactly when it
preserves binary coproducts and pushouts. -/
theorem iff_pushouts
    (F : C ⥤ D) [HasFiniteNonemptyColimits C] :
    PreservesFiniteNonemptyColimits F ↔
      PreservesColimitsOfShape (Discrete WalkingPair) F ∧
        PreservesColimitsOfShape WalkingSpan F := sorry

end PreservesFiniteNonemptyColimits.BinaryCoproducts

end CategoryTheory.Limits
