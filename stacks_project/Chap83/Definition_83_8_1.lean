module

import stacks_project.Chap83.Definition_83_8_1_InvariantFunctions
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace PreRelation Limits

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
variable (P : PreRelation U) (φ : U ⟶ X)
variable (h_invariant : P.t ≫ φ = P.s ≫ φ)

/- Definition 83.8.1 (1): for an R-invariant morphism φ : U ⟶ X, the sheaf of
R-invariant functions (φ_* 𝒪_U)^R on X_étale is the 𝒪_X-subalgebra of φ_* 𝒪_U
equalizing φ_* s^♯ and φ_* t^♯ into φ'_* 𝒪_R, where φ' = φ ∘ s = φ ∘ t. -/
@[stacks 04AA] #check
  (PreRelation.invariantFunctions P φ h_invariant :
    Sheaf (smallEtaleTopology X.left) RingCat.{u})

/- Definition 83.8.1 (2): the functions on X are the R-invariant functions on U
when the natural map 𝒪_X ⟶ (φ_* 𝒪_U)^R is an isomorphism. -/
@[stacks 04AA] #check
  (PreRelation.HasInvariantFunctions P φ h_invariant : Prop)
