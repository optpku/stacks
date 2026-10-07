module

public import stacks_project.Chap85.Lemma_85_5_5_Fiberwise
public import stacks_project.Chap85.Lemma_85_5_5_MorphismDiagram
import StacksCheckRecall

/-!
# Lemma 85.5.5

In the data of Remark 85.5.4, the morphisms of topoi `a`, `a'`, `h_total` and
`h₋₁` form a commutative square `Sh(C_total) ⟶ Sh(C'_total)` over
`Sh(D) ⟶ Sh(D')`. Equivalently the inverse images satisfy
`(a')⁻¹ ⋙ h_total⁻¹ ≅ h₋₁⁻¹ ⋙ a⁻¹`. Cases A and B of Situation 85.3.3 are
independent.
-/

@[expose] public section

open CategoryTheory

/- Lemma 85.5.5 (1)
In Situation 85.3.3 case A, with augmentations `a`, `a'` and a compatible
morphism `h₋₁`, the square of inverse images commutes:
`(a')⁻¹ ⋙ h_total⁻¹ ≅ h₋₁⁻¹ ⋙ a⁻¹`. -/
@[stacks 0D99] #check @SimplicialSites.IsCompatible.totalInverseImage_comp

/- Lemma 85.5.5 (2)
In Situation 85.3.3 case B, with augmentations `a`, `a'` and a compatible
morphism `h₋₁`, the square of inverse images commutes:
`(a')⁻¹ ⋙ h_total⁻¹ ≅ h₋₁⁻¹ ⋙ a⁻¹`. -/
@[stacks 0D99] #check @Grothendieck.IsCompatible.totalInverseImage_comp
