/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PontryaginDual.TensorHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedModule

universe v

variable {A : CochainDGAlgebra.{0, v} ℤ}
variable (N : DifferentialGradedModule.{0, v} A)
variable (M : LeftDifferentialGradedModule.{0, v} A)

/- Lemma 22.19.2 (1) (09K3): morphisms `N ⟶ Mᵛ` are canonically cochain maps
`N ⊗_A M ⟶ ℚ/ℤ[0]`. -/
@[stacks 09K3] #check
  (TensorCharacter.homEquiv N M :
    (N ⟶ LeftDifferentialGradedModule.pontryaginDual M) ≃
      (TensorProduct.complex N M ⟶ TensorCharacter.complex))

/- Lemma 22.19.2 (2) (09K3): cochain maps `N ⊗_A M ⟶ ℚ/ℤ[0]` are canonically
differential graded `A`-balanced pairings `N × M ⟶ ℚ/ℤ`. -/
@[stacks 09K3] #check
  (TensorCharacter.pairingEquiv N M :
    BalancedPairing N M ≃
      (TensorProduct.complex N M ⟶ TensorCharacter.complex))
