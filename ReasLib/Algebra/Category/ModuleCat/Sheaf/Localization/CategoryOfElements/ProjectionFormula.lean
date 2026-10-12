/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Continuous
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formula for module sheaves on a category-of-elements localization

For a set-valued sheaf `F`, this file names restriction to its category of elements, its lower
shriek, and the canonical projection-formula comparison.  Coefficients are modeled as
`ModuleCat Λ`, so the tensor product is the module tensor product rather than the cartesian
product on additive groups.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory.ModuleSheaf.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (Λ : Type w) [CommRing Λ] (F : Sheaf J (Type v))

/-- Restriction of `Λ`-module sheaves to the category-of-elements localization at `F`. -/
noncomputable abbrev restriction :
    Sheaf J (ModuleCat.{w} Λ) ⥤
      Sheaf (localizationTopology F) (ModuleCat.{w} Λ) :=
  (localizationProjection F).sheafPushforwardContinuous
    (ModuleCat.{w} Λ) (localizationTopology F) J

section LowerShriek

variable [∀ P : F.obj.Elementsᵒᵖᵒᵖ ⥤ ModuleCat.{w} Λ,
  (localizationProjection F).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [HasWeakSheafify (localizationTopology F) (ModuleCat.{w} Λ)]
variable [(J.W (A := ModuleCat.{w} Λ)).IsMonoidal]
variable [((localizationTopology F).W (A := ModuleCat.{w} Λ)).IsMonoidal]
variable [(restriction Λ F).IsRightAdjoint]

/-- Lower shriek from the category-of-elements localization, defined as the left adjoint of
restriction. -/
noncomputable abbrev lowerShriek :
    Sheaf (localizationTopology F) (ModuleCat.{w} Λ) ⥤
      Sheaf J (ModuleCat.{w} Λ) :=
  (restriction Λ F).leftAdjoint

/-- Lower shriek is left adjoint to restriction at `F`. -/
noncomputable def lowerShriekRestrictionAdj :
    lowerShriek Λ F ⊣ restriction Λ F :=
  Adjunction.ofIsRightAdjoint (restriction Λ F)

/-- The canonical oplax-monoidal structure on lower shriek, transferred from the canonical
strong monoidal structure on restriction. -/
@[implicit_reducible]
noncomputable instance lowerShriekOplaxMonoidal :
    (lowerShriek Λ F).OplaxMonoidal :=
  (lowerShriekRestrictionAdj Λ F).leftAdjointOplaxMonoidal

/-- The canonical comparison `jₗ! (G ⊗ j⁻¹ H) ⟶ jₗ! G ⊗ H`. -/
noncomputable abbrev projectionFormulaMap
    (G : Sheaf (localizationTopology F) (ModuleCat.{w} Λ))
    (H : Sheaf J (ModuleCat.{w} Λ)) :
    (lowerShriek Λ F).obj (G ⊗ (restriction Λ F).obj H) ⟶
      (lowerShriek Λ F).obj G ⊗ H :=
  (lowerShriekRestrictionAdj Λ F).projectionFormulaMap G H

/-- The category-of-elements localization of module sheaves satisfies the projection formula. -/
@[stacks 0E8I "category-of-elements localization"]
noncomputable instance lowerShriekProjectionFormula :
    (lowerShriekRestrictionAdj Λ F).ProjectionFormulaMap := sorry

/-- The category-of-elements projection formula, oriented as
`jₗ! G ⊗ H ≅ jₗ! (G ⊗ j⁻¹ H)`. -/
noncomputable abbrev projectionFormulaIso
    (G : Sheaf (localizationTopology F) (ModuleCat.{w} Λ))
    (H : Sheaf J (ModuleCat.{w} Λ)) :
    (lowerShriek Λ F).obj G ⊗ H ≅
      (lowerShriek Λ F).obj (G ⊗ (restriction Λ F).obj H) :=
  (lowerShriekRestrictionAdj Λ F).projectionFormulaMapIso G H

/-- The unit specialization `jₗ! (j⁻¹ H) ≅ jₗ! (𝟙_) ⊗ H`. -/
@[stacks 0EYY "(b)"]
noncomputable abbrev unitProjectionFormulaIso
    (H : Sheaf J (ModuleCat.{w} Λ)) :
    (lowerShriek Λ F).obj ((restriction Λ F).obj H) ≅
      (lowerShriek Λ F).obj (𝟙_ _) ⊗ H :=
  (lowerShriekRestrictionAdj Λ F).unitProjectionFormulaMapIso H

/- The `sorryAx` in the following audits is confined to the Prop-valued projection-formula
invertibility instance; both functors and the comparison morphism are explicit. -/

end LowerShriek

end CategoryTheory.ModuleSheaf.Localization
