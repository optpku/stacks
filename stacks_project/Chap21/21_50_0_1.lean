module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
import StacksCheckRecall

@[expose] public section

/-!
# Projection-formula morphism on ringed sites

The ringed-site morphism is the left projection-formula mate for the canonical derived
pullback-pushforward adjunction; its generic owner and naturality API live in `ReasLib`.
-/

/- 21.50.0.1: the canonical projection-formula morphism has the form
`R f_* E ⊗ᴸ K ⟶ R f_* (E ⊗ᴸ L f^* K)`. -/
@[stacks 0B56 "projection-formula morphism"]
#check @CategoryTheory.Adjunction.leftProjectionFormulaMate

/- Objectwise tensor-comparison form used before a coherent monoidal structure is bundled. -/
#check @CategoryTheory.Adjunction.leftProjectionFormulaMateOfIso

/- Transpose specification for the source-facing morphism. -/
#check @CategoryTheory.Adjunction.leftProjectionFormulaMateOfIso_spec

/- Transpose specification for the canonical coherent form. -/
#check @CategoryTheory.Adjunction.leftProjectionFormulaMate_spec
