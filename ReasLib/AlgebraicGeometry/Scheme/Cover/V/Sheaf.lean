module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.SheafCondition

/-!
# Standard sheaf tests for valuative covers

This module gives finite affine and singleton standard-cover tests for the
global `V`-sheaf condition.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- A scheme presheaf satisfies the standard `V` sheaf condition when it
satisfies the finite affine-family condition for every standard `V` cover. -/
abbrev satisfiesStandardVSheafProperty (F : Scheme.{u}ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {T : Scheme.{u}} [IsAffine T] (family : AffineFamilyOver T),
    AffineFamilyOver.IsStandardVCover family →
      satisfiesSheafPropertyForFamily F family.U family.map

/-- A scheme presheaf satisfies the singleton standard `V` sheaf condition
when it does so for each affine one-chart family. -/
abbrev satisfiesStandardVSingletonSheafProperty
    (F : Scheme.{u}ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (f : V ⟶ U),
    AffineFamilyOver.IsStandardVCover (AffineFamilyOver.singleton f inferInstance) →
      satisfiesSheafPropertyForFamily F
        (AffineFamilyOver.singleton f inferInstance).U
        (AffineFamilyOver.singleton f inferInstance).map

/-- The `V`-sheaf condition is equivalent to the Zariski sheaf condition
together with the standard `V` affine tests. -/
@[stacks 0ETM]
theorem satisfiesVSheafProperty_iff_zariski_and_standardV
    (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    satisfiesVSheafProperty F ↔
      satisfiesZariskiSheafProperty F ∧ satisfiesStandardVSheafProperty F := sorry

/-- Under the Zariski sheaf condition, the standard `V` affine tests reduce
to singleton standard `V` tests. -/
@[stacks 0ETM]
theorem satisfiesStandardVSheafProperty_iff_singleton
    (F : Scheme.{u}ᵒᵖ ⥤ Type v) (hzar : satisfiesZariskiSheafProperty F) :
    satisfiesStandardVSheafProperty F ↔ satisfiesStandardVSingletonSheafProperty F := sorry

end AlgebraicGeometry
