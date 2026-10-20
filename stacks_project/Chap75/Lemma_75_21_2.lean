module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Pushforward
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward

/-! # Cohomology and base change for a single derived quasi-coherent complex -/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Lemma 75.21.2: for a cartesian square of algebraic spaces over a scheme, the
geometric-point cohomology base-change criterion makes the canonical composite
`Lg^* Rf_* K ⟶ Rf'_* L(g')^* K ⟶ Rf'_* K'` invertible when `f` is quasi-compact
and quasi-separated. -/
@[stacks 0DKH] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.cohomologyBaseChange_comp_isIso :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
      (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K'),
      cohomologyBaseChangeHolds sq K K' α →
        IsIso (cohomologyBaseChangeComp g' f' f g sq K K' α))

