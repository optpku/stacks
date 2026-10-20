module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFpqc.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf

/-!
# Sheaf tests for standard fpqc covers

This module packages the local finite-affine and singleton tests for the
canonical fpqc sheaf condition.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A scheme presheaf satisfies the standard fpqc sheaf condition when it
satisfies the fixed-family condition for every finite standard fpqc cover of
an affine scheme. -/
abbrev satisfiesStandardFpqcSheafProperty (F : Scheme.{u}ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {T : Scheme.{u}} (cover : StandardFpqcCover T),
    satisfiesSheafPropertyForFamily F cover.U cover.map

/-- A scheme presheaf satisfies the affine faithfully-flat singleton sheaf
condition when it satisfies descent for every flat surjective map between
affine schemes. -/
abbrev satisfiesAffineFaithfullyFlatSingletonSheafProperty
    (F : Scheme.{u}ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {U V : Scheme.{u}} (f : V ⟶ U) [IsAffine U] [IsAffine V] [Flat f] [Surjective f],
    satisfiesSheafPropertyForFamily F (fun _ : Unit ↦ V) (fun _ ↦ f)

/-- Assuming Zariski descent, descent for every finite standard fpqc cover is
equivalent to descent for every faithfully flat map between affine schemes. -/
theorem satisfiesStandardFpqcSheafProperty_iff_affineFaithfullyFlatSingleton
    (F : Scheme.{u}ᵒᵖ ⥤ Type v) (hzar : satisfiesZariskiSheafProperty F) :
    satisfiesStandardFpqcSheafProperty F ↔
      satisfiesAffineFaithfullyFlatSingletonSheafProperty F := sorry

/-- The canonical fpqc sheaf condition is equivalent to the Zariski sheaf
condition together with descent for every finite standard fpqc cover. -/
theorem satisfiesFpqcSheafProperty_iff_zariski_and_standardFpqc
    (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    satisfiesFpqcSheafProperty F ↔
      satisfiesZariskiSheafProperty F ∧ satisfiesStandardFpqcSheafProperty F := sorry

end AlgebraicGeometry
