module

public import stacks_project.Chap78.Lemma_78_20_3_Comparison
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace

/- Remark 78.20.4: later chapters write an algebraic space `X` for the stack in sets
`𝒮_X := stackInSets X`. Under that identification the `2`-commutative square of
Lemma 78.20.3 is the familiar square with legs
`s := stackInSets.map G.s.left`, `t := stackInSets.map G.t.left` from
`stackInSets G.R.left` to `stackInSets G.U.left`, and atlas
`π := atlas G : stackInSets G.U.left ⟶ quotientStack G`, together with the canonical
`2`-cell `sourceTarget : atlasSource G ⟶ atlasTarget G`. Sections 78.22 and 78.23 later
show that this square is a `2`-fibre product and close to a `2`-coequalizer of `s` and `t`. -/
@[stacks 04M7] #check
  (@sourceTarget :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      atlasSource G ⟶ atlasTarget G)

#check
  (@stackInSets :
    ∀ {S : Scheme.{u}}, AlgebraicSpace S → StackOver.Sets (Scheme.fppfTopology.over S))

#check
  (@stackInSets.map :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      (X ⟶ Y) → CartesianBasedFunctor (stackInSets X).p (stackInSets Y).p)

#check
  (@atlas :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      CartesianBasedFunctor (stackInSets G.U.left).p (quotientStack G).p)

#check
  (@atlasSource :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      CartesianBasedFunctor (stackInSets G.R.left).p (quotientStack G).p)

#check
  (@atlasTarget :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      CartesianBasedFunctor (stackInSets G.R.left).p (quotientStack G).p)
