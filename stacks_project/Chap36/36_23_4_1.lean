/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Kunneth

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable {X Y : Over (Spec (CommRingCat.of A))}
variable (𝒰 : X.left.AffineOpenCover) (𝒱 : Y.left.AffineOpenCover)
variable (F : X.left.Modules) (G : Y.left.Modules)

/- 36.23.4.1: the canonical morphism from the total tensor product of the Čech complexes
for covers `𝒰` of `X` and `𝒱` of `Y` to the Čech complex for their product cover `𝒲` on
`X ×_S Y`, with coefficients in `p^*𝓕 ⊗ q^*𝓖`. -/
@[stacks 0FLU] #check
  (AlgebraicGeometry.Scheme.OpenCoverCech.Kunneth.comparisonOverSpec
    X.hom Y.hom 𝒰.openCover 𝒱.openCover F G :
    HomologicalComplex.tensorObj
        (AlgebraicGeometry.Scheme.OpenCoverCech.globalSectionsOverSpec
          X.hom 𝒰.openCover F)
        (AlgebraicGeometry.Scheme.OpenCoverCech.globalSectionsOverSpec
          Y.hom 𝒱.openCover G) ⟶
      AlgebraicGeometry.Scheme.OpenCoverCech.globalSectionsOverSpec
        (pullback.fst X.hom Y.hom ≫ X.hom)
        (AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight
          𝒰.openCover 𝒱.openCover X.hom Y.hom)
        (AlgebraicGeometry.Scheme.Modules.externalTensorProduct
          X.hom Y.hom F G))
