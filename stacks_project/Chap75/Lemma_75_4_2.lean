module

public import stacks_project.Chap75.Lemma_75_4_2_Pullback
public import stacks_project.Chap75.Lemma_75_4_2_SmallEtale
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 75.4.2: for a scheme `X`, the exact pullback `ε^*` along
`ε : (X_étale, 𝒪_étale) ⟶ (X_Zar, 𝒪_X)` induces an equivalence
`Scheme.DerivedQCoh X ⥤ DerivedQCoh.SmallEtale X`. -/
@[stacks 071Q] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.epsilonStar_isEquivalence :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      Functor.IsEquivalence (AlgebraicGeometry.Scheme.DerivedQCoh.epsilonStar X))
