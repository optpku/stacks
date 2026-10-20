module

import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Proper
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 30.26.8: in a cartesian square of schemes, pullback preserves properness over the base
of the closed support of a finite-type quasi-coherent module. -/
@[stacks 0CYT] #check (
  AlgebraicGeometry.Scheme.Modules.closedSupport_pullback_isProperOver :
    ∀ {X' X S' S : AlgebraicGeometry.Scheme.{u}}
      {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
      (sq : CategoryTheory.IsPullback g' f' f g)
      [AlgebraicGeometry.LocallyOfFiniteType f] (ℱ : X.Modules)
      [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
      [AlgebraicGeometry.ClosedSubset.IsProperOver f
        (AlgebraicGeometry.Scheme.Modules.closedSupport ℱ)],
      AlgebraicGeometry.ClosedSubset.IsProperOver f'
        (AlgebraicGeometry.Scheme.Modules.closedSupport
          ((AlgebraicGeometry.Scheme.Modules.pullback g').obj ℱ)))
