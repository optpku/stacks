/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.ProjectionFormula
import StacksCheckRecall

/-!
# Lemma 18.27.9

Extension from a slice site satisfies the projection formula.  ReasLib owns the explicit
comparison morphism, its inferable invertibility property, and the resulting canonical
isomorphism.
-/

@[expose] public section

/- Lemma 18.27.9 (0E8I), comparison data:
`jₗ! (G ⊗ j⁻¹ F) ⟶ jₗ! G ⊗ F`. -/
@[stacks 0E8I "comparison"]
#check @SheafOfModules.Localization.projectionFormulaMap

/- Lemma 18.27.9 (0E8I), reusable property: the localization adjunction satisfies the
projection formula. -/
@[stacks 0E8I "property"]
#check @SheafOfModules.Localization.lowerShriekProjectionFormula

/- Lemma 18.27.9 (0E8I), source orientation:
`jₗ! G ⊗ F ≅ jₗ! (G ⊗ j⁻¹ F)`. -/
@[stacks 0E8I "isomorphism"]
#check @SheafOfModules.Localization.projectionFormulaIso
