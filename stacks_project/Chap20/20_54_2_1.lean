/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
import StacksCheckRecall

@[expose] public section

/-!
# Projection-formula morphism

The adjunction mate and its naturality API are owned by `ReasLib`.  The objectwise comparison
bridge records the textbook presentation; coherent monoidal functors use the bundled owner.
-/

/- 20.54.2.1: the canonical projection-formula morphism of a monoidal adjunction is the mate
`R E ⊗ K ⟶ R (E ⊗ L K)`. -/
@[stacks 0B53]
#check @CategoryTheory.Adjunction.leftProjectionFormulaMate

/- The source's objectwise family of tensor-comparison isomorphisms gives the corresponding raw
mate before the comparisons are bundled as a coherent monoidal structure. -/
#check @CategoryTheory.Adjunction.leftProjectionFormulaMateOfIso

/- Transposing the raw mate recovers the explicit projection-formula map. -/
#check @CategoryTheory.Adjunction.leftProjectionFormulaMateOfIso_spec

/- Transpose specification for the canonical coherent form. -/
#check @CategoryTheory.Adjunction.leftProjectionFormulaMate_spec

/- The opposite tensor order remains a separate companion without assuming a braiding. -/
#check @CategoryTheory.Adjunction.projectionFormulaMate
