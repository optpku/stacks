module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.CharacterTwist
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {W U : AlgebraicSpace S} {G : Type u} [Group G] [Finite G]
variable (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)

/- Lemma 69.7.1. With `S`, `W`, `G`, `U`, `χ` as in Lemma 69.6.5, tensoring a
quasi-coherent `𝒪_U`-module with `ℤ̲(χ)` preserves quasi-coherence. -/
@[stacks 072A] #check
  (AlgebraicGeometry.AlgebraicSpace.tensorIntegerCharacterModule_isQuasicoherent ρ q χ :
    ∀ (F : U.Modules) [F.IsQuasicoherent],
      (AlgebraicGeometry.AlgebraicSpace.tensorIntegerCharacterModule ρ q χ F).IsQuasicoherent)
