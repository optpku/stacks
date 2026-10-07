module

public import stacks_project.Chap70.Lemma_70_12_1_Approximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.12.1: a proper morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, with `Y` quasi-compact and quasi-separated, presents `X` as a
directed inverse limit of algebraic spaces `X_i` over `Y` whose transition maps
and morphisms `X ⟶ X_i` are closed immersions and whose structure maps
`X_i ⟶ Y` are proper and of finite presentation. -/
@[stacks 0A0W] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_properApproximation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.Proper f]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
      Nonempty (ProperApproximation f))
