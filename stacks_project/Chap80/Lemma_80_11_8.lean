module

public import stacks_project.Chap80.Lemma_80_11_8_DescentDatum
public import stacks_project.Chap80.Lemma_80_11_8_Pullback

/-!
# Effective descent of fppf torsors along an fppf covering
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupAlgebraicSpace
open GroupAlgebraicSpace.Torsor

noncomputable section

universe u v

namespace AlgebraicGeometry.GroupAlgebraicSpace.Torsor
namespace DescentDatum

/-- Lemma 80.11.8: let `{S_i → S}_{i ∈ I}` be a covering of `(Sch/S)_fppf`. Let
`G` be a group algebraic space over `S`, and denote `G_i = G_{S_i}` the base
changes. Suppose given for each `i ∈ I` an fppf `G_i`-torsor `X_i` over `S_i`,
and for each `i, j ∈ I` a `G_{S_i ×_S S_j}`-equivariant isomorphism
`φ_ij : X_i ×_S S_j ⟶ S_i ×_S X_j` satisfying the cocycle condition over every
`S_i ×_S S_j ×_S S_k`. Then there exists an fppf `G`-torsor `X` over `S` whose
base change to `S_i` is isomorphic to `X_i` such that we recover the descent
datum `φ_ij`. The hypothesis `[Small.{u} I]` is the size condition of Spaces,
Lemma 65.8.4 making `∐ X_i` an algebraic space. -/
@[stacks 04U1]
theorem exists_fppfTorsor {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {Si : I → Over S}
    {G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 S)))}
    (D : DescentDatum Si G) : Nonempty D.Effectiveness := sorry

end DescentDatum
end AlgebraicGeometry.GroupAlgebraicSpace.Torsor
