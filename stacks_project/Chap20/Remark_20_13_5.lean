/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Leray.SourceScalars
import StacksCheckRecall

@[expose] public section

/-!
# Source scalars on the Leray spectral sequence

The reusable owner separates the module-valued Leray realization from its underlying additive
comparison.  The comparison is a morphism of spectral sequences and is invertible from `E₂`
onward, so compatibility with differentials and successive-page identifications is part of the
API rather than an unstructured family of objectwise isomorphisms.
-/

/- Remark 20.13.5: for a module sheaf, the Leray spectral sequence carries a
`Γ(X, 𝒪_X)`-module structure, and forgetting that structure recovers the ordinary Leray spectral
sequence from the second page onward. -/
@[stacks 01F3]
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.SourceScalars.ofModule

/- The bounded-below derived form is the reusable generalization of the source statement. -/
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.SourceScalars.nonempty
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.SourceScalars.Comparison
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.SourceScalars.Comparison.isIsoFromTwo
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.SourceScalars.page_isIsomorphic

/- The source scalar ring comes from the canonical intermediate ringed space
`(Y, f_* 𝒪_X)` and is canonically identified with `Γ(X, 𝒪_X)`. -/
#check @AlgebraicGeometry.RingedSpace.Hom.PushforwardStructure.target
#check @AlgebraicGeometry.RingedSpace.Hom.PushforwardStructure.lift
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.SourceScalars.ring_isIsomorphic

/- The linear Leray realization is independently reusable before specializing the target
structure sheaf. -/
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.Linear.Realization
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.Linear.functorial
