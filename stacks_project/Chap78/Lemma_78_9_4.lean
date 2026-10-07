module

public import stacks_project.Chap78.Lemma_78_9_4_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 78.9.4: Let `S` be a scheme. Let `G` be a group algebraic space over `S`.
Let `X` be an algebraic space over `S` with a `G`-action. Then `X` is an fppf
`G`-torsor in the sense of Definition 78.9.3 if and only if `X` is a `G`-torsor
on `(Sch/S)_fppf` in the sense of Definition 21.4.1. -/
@[stacks 04TZ]
#check (AlgebraicGeometry.GroupAlgebraicSpace.isStandardTorsor_iff_isSheafTorsor :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (G : AlgebraicGeometry.GroupAlgebraicSpace
      (AlgebraicGeometry.AlgebraicSpace.ofOver (Over.mk (𝟙 S))))
    (X : AlgebraicGeometry.GroupAlgebraicSpace.Action G),
    AlgebraicGeometry.GroupAlgebraicSpace.IsStandardTorsor G X
      AlgebraicGeometry.StandardTopology.fppf ↔
      AlgebraicGeometry.GroupAlgebraicSpace.IsSheafTorsor G X)
