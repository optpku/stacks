module

public import stacks_project.Chap78.Lemma_78_20_3_Comparison
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace

/- Lemma 78.20.3: there is a canonical `2`-morphism `α : π ∘ s ⟶ π ∘ t` making the square
`𝒮_R ⇉ 𝒮_U ⟶ [U/R]` `2`-commutative. -/
@[stacks 044S] #check
  (@sourceTarget :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      atlasSource G ⟶ atlasTarget G)
