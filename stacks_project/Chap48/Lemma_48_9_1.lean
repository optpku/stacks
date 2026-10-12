/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.InternalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)
variable [RingedSpace.IsClosedImmersion i]

/- Lemma 48.9.1 (1): the functor `homFromStructureSheaf`, representing
`𝒥 ↦ Hom(𝒪_Z, 𝒥)`, is right adjoint to pushforward along the closed immersion `i`. -/
@[stacks 0A75] #check
  (AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedImmersion.adjunction
      i (RingedSpace.IsClosedImmersion.isClosedEmbedding (i := i)) :
    RingedSpace.Hom.pushforward i ⊣
      AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedImmersion.homFromStructureSheaf
        i (RingedSpace.IsClosedImmersion.isClosedEmbedding (i := i)))

/- Lemma 48.9.1 (2): over `U ⊆ X`, hence over `i ⁻¹ᵁ U ⊆ Z`, the counit identifies
sections of `Hom(𝒪_Z, 𝒥)` bijectively with the sections of `𝒥` annihilated by every
section of the ideal sheaf of `i`. -/
@[stacks 0A75] #check
  (AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedImmersion.homFromStructureSheaf_sections_bijOn
      i (RingedSpace.IsClosedImmersion.isClosedEmbedding (i := i)) :
    ∀ (𝒥 : X.Modules) (U : TopologicalSpace.Opens X.carrier),
      Set.BijOn
        (((AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedImmersion.adjunction
          i (RingedSpace.IsClosedImmersion.isClosedEmbedding (i := i))).counit.app 𝒥).val.app
            (op U))
        Set.univ
        {s | ∀ r : (RingedSpace.Hom.idealSheaf i).val.obj (op U),
          ((RingedSpace.Hom.idealSheafι i).val.app (op U) r) • s = 0})
