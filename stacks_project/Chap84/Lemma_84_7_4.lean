/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.EtaleFppfDescent

/-!
# Lemma 84.7.4

For an object of `D_QCoh(𝒪_X)` on an algebraic space, the canonical maps
`Lπ_X^* K ⟶ Rε_{X,*}(La_X^* K)` and `K ⟶ Ra_{X,*}(La_X^* K)` are isomorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 84.7.4 (1): the canonical map `Lπ_X^* K ⟶ Rε_{X,*}(La_X^* K)` is an
isomorphism. -/
@[stacks 0DGR] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.piPullbackDerivedUnit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (K : DerivedQCoh X),
    IsIso (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.piPullbackDerivedUnit
      ((AlgebraicGeometry.AlgebraicSpace.AssociatedModule.moduleCarrierLiftDerived X).obj K.obj)))

/- Lemma 84.7.4 (2): the canonical map `K ⟶ Ra_{X,*}(La_X^* K)` is an
isomorphism. -/
@[stacks 0DGR] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.aDerivedUnit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (K : DerivedQCoh X),
    IsIso (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.aDerivedUnit
      ((AlgebraicGeometry.AlgebraicSpace.AssociatedModule.moduleCarrierLiftDerived X).obj K.obj)))

end

end
