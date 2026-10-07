module

public import stacks_project.Chap78.Lemma_78_12_5_Colimits
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits

/- Lemma 78.12.5: the category of quasi-coherent modules on a groupoid in algebraic
spaces `(U, R, s, t, c)` over `B` has colimits. -/
@[stacks 077X] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.hasColimitsOfSize :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      HasColimitsOfSize.{u, u} G.QCoh)
