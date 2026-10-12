/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_29_4_Neighborhood
public import stacks_project.Chap66.Lemma_66_29_4_Stalk

/-!
# Lemma 66.29.4

The étale stalk of a quasi-coherent module on an algebraic space is the tensor product of
the Zariski stalk of its pullback along a scheme étale neighbourhood with the étale local
ring at the geometric point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood
open AlgebraicGeometry.AlgebraicSpace.Modules
open etaleLocalRing_etaleNeighborhood ModuleCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Lemma 66.29.4: let `S` be a scheme, let `X` be an algebraic space over `S`, and let `F` be
a quasi-coherent `𝒪_X`-module. Let `xbar` be a geometric point of `X` lying over
`xbar.image ∈ |X|`, and let `φ : (U, ubar) → (X, xbar)` be a scheme étale neighbourhood, with
`u` the image of `ubar`. Then there is a canonical identification
`(φ* F)_u ⊗_{𝒪_{U,u}} 𝒪_{X, xbar} ≅ F_{xbar}`
as modules over `etaleLocalRing X xbar`, where the scalar map is
`fromZariskiStalk N : 𝒪_{U,u} →+* 𝒪_{X, xbar}`. -/
@[stacks 05VP]
theorem pullbackStalkTensorHom_isIso (F : X.Modules) [F.IsQuasicoherent]
    (xbar : GeometricPoint X) (N : SmallEtaleNeighborhood xbar) :
    IsIso (pullbackStalkTensorHom F N) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
