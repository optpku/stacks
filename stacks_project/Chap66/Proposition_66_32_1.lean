/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap66.Proposition_66_32_1_Functor
public import stacks_project.Chap66.Proposition_66_32_1_Groupoid

/-!
# Quasi-coherent modules and étale presentations

For an algebraic space `X` over `S` and a surjective étale atlas `φ : U ⟶ X`, quasi-coherent
`𝒪_X`-modules are equivalent to quasi-coherent modules on the associated étale groupoid
`(U, R, s, t, c)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- Proposition 66.32.1: Let `φ : U ⟶ X` be a surjective étale morphism from a scheme to an
algebraic space over `S`, with associated étale groupoid `(U, R, s, t, c)`. For a
quasi-coherent `𝒪_X`-module `F`, the pullback `φ* F` carries a canonical isomorphism
`α : t* φ* F ⟶ s* φ* F` satisfying GroupoidScheme.Cocycle and GroupoidScheme.Unit, and
`F ↦ (φ* F, α)` is an equivalence `QCoh X ≌ (atlasGroupoid φ).QCoh`. -/
@[stacks 03M3]
instance toGroupoid_isEquivalence (φ : ofOver U ⟶ X) [Etale φ]
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ] :
    (toGroupoid φ).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
