/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_12_6_Abelian
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 78.12.6: if the source and target maps of a groupoid in algebraic spaces over `B`
are flat, then its category of equivariant quasi-coherent modules is abelian. -/
@[stacks 06VZ]
#check (@AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.abelian :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B)
    [AlgebraicGeometry.AlgebraicSpace.Flat G.s.left]
    [AlgebraicGeometry.AlgebraicSpace.Flat G.t.left],
    CategoryTheory.Abelian G.QCoh)
