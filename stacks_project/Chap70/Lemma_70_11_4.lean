module

public import stacks_project.Chap70.Lemma_70_11_4_Approximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.11.4: a closed immersion `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, with `Y` quasi-compact and quasi-separated, presents `X` as a
directed inverse limit of algebraic spaces `X_i` over `Y` whose transition maps
are closed immersions and whose structure maps `X_i ⟶ Y` are closed immersions
of finite presentation. -/
@[stacks 0A0U] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_closedImmersionApproximation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.IsClosedImmersion f]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
      Nonempty (ClosedImmersionApproximation f))
