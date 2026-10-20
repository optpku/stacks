/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Criteria

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.21.1: for a cartesian square of algebraic spaces over S and a map
L(g')^* K ⟶ K', the geometric-point cohomology base-change criterion is equivalent to
the scheme criterion on every compatible étale chart and on one such surjective chart. -/
@[stacks 0DKG] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.cohomologyBaseChange_tfae_etale :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K'),
    List.TFAE
      [ cohomologyBaseChangeHolds sq K K' α
      , ∀ c : EtaleBaseChangeChart g' f' f g, c.schemeHolds sq K K' α
      , ∃ c : EtaleBaseChangeChart g' f' f g,
          AlgebraicSpace.Surjective (c.toX' sq) ∧ c.schemeHolds sq K K' α ])

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
