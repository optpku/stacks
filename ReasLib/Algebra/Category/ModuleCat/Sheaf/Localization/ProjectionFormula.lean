/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formula for localization of module sheaves

This file specializes the generic projection-formula API to extension from a slice site.  The
comparison morphism is explicit, while invertibility is recorded once as an inferable property
of the localization adjunction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v w z

namespace SheafOfModules.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{w}) (U : C)
variable [MonoidalCategory (SheafOfModules.{z} (R.over U))]
variable [MonoidalCategory (SheafOfModules.{z} R)]
variable [(restriction R U : SheafOfModules.{z} R ⥤
  SheafOfModules.{z} (R.over U)).IsRightAdjoint]
variable [(restriction R U : SheafOfModules.{z} R ⥤
  SheafOfModules.{z} (R.over U)).LaxMonoidal]

/-- The canonical oplax-monoidal structure on extension from the slice, transferred from its
lax-monoidal right adjoint.  Reducibility lets typeclass search recover the associated
`Adjunction.IsMonoidal` instance without a local instance pin. -/
@[implicit_reducible]
noncomputable instance lowerShriekOplaxMonoidal :
    (lowerShriek R U : SheafOfModules.{z} (R.over U) ⥤
      SheafOfModules.{z} R).OplaxMonoidal :=
  (lowerShriekRestrictionAdj R U).leftAdjointOplaxMonoidal

/-- The canonical localization projection-formula morphism
`jₗ! (G ⊗ j⁻¹ F) ⟶ jₗ! G ⊗ F`. -/
@[stacks 0E8I "comparison"]
noncomputable abbrev projectionFormulaMap
    (G : SheafOfModules.{z} (R.over U)) (F : SheafOfModules.{z} R) :
    (lowerShriek R U).obj (G ⊗ (restriction R U).obj F) ⟶
      (lowerShriek R U).obj G ⊗ F :=
  (lowerShriekRestrictionAdj R U).projectionFormulaMap G F

/-- Extension from a slice site satisfies the projection formula. -/
@[stacks 0E8I]
noncomputable instance lowerShriekProjectionFormula :
    (lowerShriekRestrictionAdj R U).ProjectionFormulaMap := sorry

/-- The localization projection formula in the source orientation
`jₗ! G ⊗ F ≅ jₗ! (G ⊗ j⁻¹ F)`. -/
@[stacks 0E8I "isomorphism"]
noncomputable abbrev projectionFormulaIso
    (G : SheafOfModules.{z} (R.over U)) (F : SheafOfModules.{z} R) :
    (lowerShriek R U).obj G ⊗ F ≅
      (lowerShriek R U).obj (G ⊗ (restriction R U).obj F) :=
  (lowerShriekRestrictionAdj R U).projectionFormulaMapIso G F

/-- The unit specialization of the localization projection formula,
`jₗ! (j⁻¹ F) ≅ jₗ! (𝟙_) ⊗ F`. -/
noncomputable abbrev unitProjectionFormulaIso (F : SheafOfModules.{z} R) :
    (lowerShriek R U).obj ((restriction R U).obj F) ≅
      (lowerShriek R U).obj (𝟙_ _) ⊗ F :=
  (lowerShriekRestrictionAdj R U).unitProjectionFormulaMapIso F

end SheafOfModules.Localization
