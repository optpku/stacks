module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.Descent
import StacksCheckRecall

/-!
# Effective descent of fppf torsors along an fppf covering
-/

open CategoryTheory

universe u v

/- Lemma 80.11.8: let `{S_i → S}_{i ∈ I}` be a covering of `(Sch/S)_fppf`. Let
`G` be a group algebraic space over `S`, and denote `G_i = G_{S_i}` the base
changes. Suppose given for each `i ∈ I` an fppf `G_i`-torsor `X_i` over `S_i`,
and for each `i, j ∈ I` a `G_{S_i ×_S S_j}`-equivariant isomorphism
`φ_ij : X_i ×_S S_j ⟶ S_i ×_S X_j` satisfying the cocycle condition over every
`S_i ×_S S_j ×_S S_k`. Then there exists an fppf `G`-torsor `X` over `S` whose
base change to `S_i` is isomorphic to `X_i` such that we recover the descent
datum `φ_ij`. The hypothesis `[Small.{u} I]` is the size condition of Spaces,
Lemma 65.8.4 making `∐ X_i` an algebraic space. -/
@[stacks 04U1]
#check (AlgebraicGeometry.GroupAlgebraicSpace.Torsor.DescentDatum.exists_fppfTorsor :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {I : Type v} [Small.{u} I]
    {Si : I → CategoryTheory.Over S}
    {G : AlgebraicGeometry.GroupAlgebraicSpace
      (AlgebraicGeometry.AlgebraicSpace.ofOver (CategoryTheory.Over.mk (𝟙 S)))}
    (D : AlgebraicGeometry.GroupAlgebraicSpace.Torsor.DescentDatum Si G),
      Nonempty D.Effectiveness)
