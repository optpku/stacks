module

public import stacks_project.Chap78.Lemma_78_20_2_Atlas
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace

/- Lemma 78.20.2 (1): there is a canonical `1`-morphism `π : 𝒮_U ⟶ [U/R]` of stacks in
groupoids over `(Sch/S)_fppf`. -/
@[stacks 044R] #check
  (@atlas :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      CartesianBasedFunctor (stackInSets G.U.left).p (quotientStack G).p)

/- Lemma 78.20.2 (2): there is a canonical `1`-morphism `[U/R] ⟶ 𝒮_B` of stacks in
groupoids over `(Sch/S)_fppf`. -/
@[stacks 044R] #check
  (@toBase :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      CartesianBasedFunctor (quotientStack G).p (stackInSets B).p)

/- Lemma 78.20.2 (3): the composite `𝒮_U ⟶ 𝒮_B` is the `1`-morphism associated to the
structure morphism `U ⟶ B`. -/
@[stacks 044R] #check
  (@atlas_comp_toBase :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      (atlas G).comp (toBase G) ≅ stackInSets.map G.U.hom)
