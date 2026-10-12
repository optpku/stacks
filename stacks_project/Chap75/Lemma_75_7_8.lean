/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_7_8_ClosedSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 75.7.8: in a cartesian diagram of algebraic spaces over a scheme `S`
with `f : X ⟶ Y` locally of finite type, if `F` is a finite type quasi-coherent
`𝒪_X`-module whose support is proper over `Y`, then the support of
`(pullback g').obj F` is proper over `Y'`. -/
@[stacks 0CZJ] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport_pullback_isProperOver :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X' X Y' Y : AlgebraicGeometry.AlgebraicSpace S}
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y},
      IsPullback g' f' f g →
        ∀ [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
          (F : X.Modules)
          [F.IsFiniteType] [F.IsQuasicoherent]
          [AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver f
            (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport F)],
          AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver f'
            (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport
              ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback g').obj F)))
