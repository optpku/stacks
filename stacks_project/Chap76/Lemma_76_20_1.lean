/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_20_1_InfinitesimalLifting
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.20.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `x` be a point of `X`. Assume that `Y` is
locally Noetherian and `f` is locally of finite type. Then smoothness of `f`
at `x` is equivalent to the infinitesimal lifting property at `x` against
surjections of local rings with square-zero kernel, and equivalently against
small extensions. -/
@[stacks 0APN] #check
  (AlgebraicGeometry.AlgebraicSpace.smoothAt_tfae_infinitesimalLifting :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X)
      [IsLocallyNoetherian Y] [LocallyOfFiniteType f],
      List.TFAE
        [ SmoothAt f x
        , HasSquareZeroLiftingAt f x
        , HasSmallExtensionLiftingAt f x ])

end AlgebraicGeometry.AlgebraicSpace
