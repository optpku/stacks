module

public import stacks_project.Chap75.Lemma_75_7_4_Preimage
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 75.7.4: in a cartesian diagram of algebraic spaces over a scheme `S`,
if `f : X ⟶ Y` is locally of finite type and a closed subset `T ⊆ Points X` is
proper over `Y`, then its inverse image in `X'` is a closed subset of `Points X'`
proper over `Y'`. -/
@[stacks 0CZF] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver.preimage :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X' X Y' Y : AlgebraicGeometry.AlgebraicSpace S}
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y},
      IsPullback g' f' f g →
        ∀ [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
          (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points X))
          [AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver f T],
          AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver f'
            (T.preimage (AlgebraicGeometry.AlgebraicSpace.Points.continuous_map g')))
