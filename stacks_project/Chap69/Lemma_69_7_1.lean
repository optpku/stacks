/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap69.Lemma_69_7_1_Tensor

/-!
# Lemma 69.7.1

With `S`, `W`, `G`, `U`, `χ` as in Lemma 69.6.5, the integer character twist of a
quasi-coherent `𝒪_U`-module remains quasi-coherent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {W U : AlgebraicSpace S} {G : Type u} [Group G] [Finite G]
variable (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)

/-- Lemma 69.7.1: With `S`, `W`, `G`, `U`, `χ` as in Lemma 69.6.5. If `F` is a
quasi-coherent `𝒪_U`-module, then so is `F ⊗_ℤ ℤ̲(χ)`. -/
@[stacks 072A, instance]
instance tensorIntegerCharacterModule_isQuasicoherent (F : U.Modules)
    [F.IsQuasicoherent] :
    (tensorIntegerCharacterModule ρ q χ F).IsQuasicoherent :=
  sorry

/-- Explicit-hypothesis form of Lemma 69.7.1. -/
theorem tensorIntegerCharacterModule_isQuasicoherentOf {F : U.Modules}
    (hF : F.IsQuasicoherent) :
    (tensorIntegerCharacterModule ρ q χ F).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
