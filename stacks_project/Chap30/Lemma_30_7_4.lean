/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.FlatBaseChange
import StacksCheckRecall

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.Hom
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

/- Lemma 30.7.4: in a cartesian square of schemes, tensoring the pullback of a higher direct
image with a quasi-coherent module flat over the original base identifies it with the higher
direct image of the tensor product of the pulled-back modules. -/
@[stacks 0GN5] #check
  (AlgebraicGeometry.Scheme.flatBaseChange_higherDirectImage_isomorphic :
    ∀ {X' X S' S : Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (𝒢 : S'.Modules) [𝒢.IsQuasicoherent]
      (hflat : Scheme.Modules.flatOver 𝒢 g) (i : ℕ),
      IsIsomorphic
        (𝒢 ⊗ (Scheme.Modules.pullback g).obj
          (higherDirectImageModule f.toShHom ℱ i))
        (higherDirectImageModule f'.toShHom
          (((Scheme.Modules.pullback f').obj 𝒢) ⊗
            ((Scheme.Modules.pullback g').obj ℱ)) i))
