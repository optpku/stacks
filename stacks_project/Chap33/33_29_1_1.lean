/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Kunneth

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.OpenCoverCech
open AlgebraicGeometry.Scheme.OpenCoverCech.Kunneth
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {k : Type u} [Field k]
variable {X Y : Over (Spec (CommRingCat.of k))}
variable (𝒰 : X.left.AffineOpenCover) (𝒱 : Y.left.AffineOpenCover)
variable [Finite 𝒰.I₀] [Finite 𝒱.I₀]
variable (ℱ : X.left.Modules) (𝒢 : Y.left.Modules)

/- 33.29.1.1: the Künneth comparison maps the tensor total of the two pushed-forward Čech
complexes to the pushed-forward Čech complex of the product cover with external-tensor
coefficients. -/
@[stacks 0BEE] #check
  (comparison
    X.hom Y.hom 𝒰.openCover 𝒱.openCover ℱ 𝒢 :
    HomologicalComplex.tensorObj
        (pushforward X.hom
          (fun i : 𝒰.I₀ ↦ (𝒰.openCover.f i).opensRange) ℱ)
        (pushforward Y.hom
          (fun j : 𝒱.I₀ ↦ (𝒱.openCover.f j).opensRange) 𝒢) ⟶
      pushforward
        (pullback.fst X.hom Y.hom ≫ X.hom)
        (fun ij : 𝒰.I₀ × 𝒱.I₀ ↦
          ((AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight
            𝒰.openCover 𝒱.openCover X.hom Y.hom).f ij).opensRange)
        (AlgebraicGeometry.Scheme.Modules.externalTensorProduct
          X.hom Y.hom ℱ 𝒢))
