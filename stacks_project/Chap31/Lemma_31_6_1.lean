/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Pushforward
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 31.6.1: for an affine morphism of schemes `f : X ⟶ S` and a quasi-coherent
`𝒪_X`-module `ℱ`, the weakly associated points of `f_*ℱ` lie in the image under `f` of the
weakly associated points of `ℱ`. -/
@[stacks 05EX] #check
  (AlgebraicGeometry.Scheme.Modules.weakAss_pushforward_subset_image_of_isAffine :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ((Scheme.Modules.pushforward f).obj ℱ).weakAss ⊆ f.base '' ℱ.weakAss)
