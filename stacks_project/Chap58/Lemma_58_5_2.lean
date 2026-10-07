module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 58.5.2 (1): the category of finite étale schemes over a scheme has finite limits. -/
@[stacks 0BN9] #check (AlgebraicGeometry.Scheme.finiteEtale_hasFiniteLimits :
  ∀ (X : Scheme.{u}), HasFiniteLimits (AlgebraicGeometry.Scheme.FiniteEtale X))

/- Lemma 58.5.2 (2): the category of finite étale schemes over a scheme has finite colimits. -/
@[stacks 0BN9] #check (AlgebraicGeometry.Scheme.finiteEtale_hasFiniteColimits :
  ∀ (X : Scheme.{u}), HasFiniteColimits (AlgebraicGeometry.Scheme.FiniteEtale X))

/- Lemma 58.5.2 (3): base change on finite étale schemes is exact. -/
@[stacks 0BN9] #check (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_exact :
  ∀ {X X' : Scheme.{u}} (f : X' ⟶ X),
    exactFunctor (AlgebraicGeometry.Scheme.FiniteEtale X) (AlgebraicGeometry.Scheme.FiniteEtale X')
      (AlgebraicGeometry.Scheme.finiteEtaleBaseChange f))
