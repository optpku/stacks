module

public import stacks_project.Chap75.Lemma_75_7_7_ModuleSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 75.7.7: for a locally of finite type morphism `f : X ⟶ Y` of algebraic
spaces over a scheme `S` and a finite-type quasi-coherent `𝒪_X`-module `F`,
properness of the support of `F` over `Y`, properness of the scheme-theoretic
support of `F` over `Y`, and descent from a proper closed subspace are
equivalent. -/
@[stacks 0CZI] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport_isProperOver_tfae :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent],
      List.TFAE [
        AlgebraicGeometry.AlgebraicSpace.ClosedSubset.IsProperOver f
          (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport F),
        AlgebraicGeometry.AlgebraicSpace.Proper
          ((AlgebraicGeometry.AlgebraicSpace.Modules.schemeTheoreticSupport F).ι ≫ f),
        ∃ (Z : AlgebraicGeometry.AlgebraicSpace.ClosedSubspace X)
          (G : Z.X.Modules),
          G.IsFiniteType ∧ G.IsQuasicoherent ∧
            AlgebraicGeometry.AlgebraicSpace.Proper (Z.ι ≫ f) ∧
            Nonempty
              ((AlgebraicGeometry.AlgebraicSpace.Modules.pushforward Z.ι).obj G ≅ F)])
