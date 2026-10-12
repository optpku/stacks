/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_29_5_Comparison

/-!
# Lemma 66.29.5

The étale stalk of the pullback of a quasi-coherent module along a morphism of algebraic
spaces is the tensor product of the stalk of the original module with the étale local ring
of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.Modules
open ModuleCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 66.29.5: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. Let `G` be a quasi-coherent `𝒪_Y`-module. Let `xbar` be a geometric point of `X`
and let `ȳ = xbar.map f` be the image in `Y`. Then there is a canonical isomorphism
`(f* G)_{xbar} ≅ G_ȳ ⊗_{𝒪_{Y, ȳ}} 𝒪_{X, xbar}`
of modules over `etaleLocalRing X xbar`. -/
@[stacks 05VQ]
instance pullbackStalkComparison_isIso (f : X ⟶ Y) (G : Y.Modules) [G.IsQuasicoherent]
    (xbar : GeometricPoint X) :
    IsIso (pullbackStalkComparison f G xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
