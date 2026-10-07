module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Equivalence
import StacksCheckRecall

@[expose] public section

universe u

/- Proposition 35.8.9 (1): the associated-module functor from quasi-coherent modules
on a scheme to quasi-coherent modules on any big standard site is an equivalence. -/
@[stacks 03DX] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor.isEquivalence :
    ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u}),
      (AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor τ S).IsEquivalence)

/- Proposition 35.8.9 (2): the associated-module functor from quasi-coherent modules
on a scheme to quasi-coherent modules on its small Zariski or étale site is an equivalence. -/
@[stacks 03DX] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor.isEquivalence :
    ∀ (σ : AlgebraicGeometry.SmallStandardTopology) (S : AlgebraicGeometry.Scheme.{u}),
      (AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor σ S).IsEquivalence)
