module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 75.7.1: for a locally of finite type morphism of algebraic spaces, properness
of the reduced induced closed subspace, of some closed-subspace structure, and of every
closed-subspace structure on a fixed closed subset are equivalent. -/
@[stacks 0CZC] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubset.isProperOver_tfae :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points X)),
      List.TFAE [
        AlgebraicGeometry.AlgebraicSpace.Proper
          ((AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure.reduced T).ι ≫ f),
        ∃ Z : AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure T,
          AlgebraicGeometry.AlgebraicSpace.Proper (Z.ι ≫ f),
        ∀ Z : AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure T,
          AlgebraicGeometry.AlgebraicSpace.Proper (Z.ι ≫ f)])
