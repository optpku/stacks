/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap76.Lemma_76_15_12_Differentials
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {B X Z Z' : AlgebraicSpace S}
variable (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
variable [IsUniversalFirstOrder i h'] [FormallyUnramified h]
variable (w : i ≫ h' = h)

/- The induced map is the pullback of `dh'`, after identifying `h^* Ω_{X/B}`
with `i^* (h')^* Ω_{X/B}`. Source notation `Ω_{Z'/B} ⊗ 𝒪_Z` is
`(Modules.pullback i).obj (relativeDifferentials (h' ≫ f))`. -/
#check
  (pullbackDifferentialsComparison i h' h f w :
    (Modules.pullback h).obj (relativeDifferentials f) ⟶
      (Modules.pullback i).obj (relativeDifferentials (h' ≫ f)))

/- Lemma 76.15.12: Let `S` be a scheme, `B` an algebraic space over `S`, and
`h : Z ⟶ X` a formally unramified morphism of algebraic spaces over `B`. If
`i : Z ⟶ Z'` is the universal first-order thickening of `Z` over `X` with
structure morphism `h' : Z' ⟶ X`, then the canonical comparison
`dh' : (h')^* Ω_{X/B} ⟶ Ω_{Z'/B}` pulls back along `i` to an isomorphism
`h^* Ω_{X/B} ⟶ i^* Ω_{Z'/B}`. -/
@[stacks 060E]
#check
  (pullbackDifferentialsComparison_isIso i h' h f w :
    IsIso (pullbackDifferentialsComparison i h' h f w))
