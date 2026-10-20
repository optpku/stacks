/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- 75.21.0.1: a commutative square of algebraic spaces and a morphism
L(g')^* K ⟶ K' induce at every geometric point and degree the canonical map
from H^i(K_{x̄} ⊗ᴸ_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'}), extended from
𝒪_{X,x̄} ⊗[𝒪_{Y,ȳ}] 𝒪_{Y',ȳ'} to 𝒪_{X',x̄'}, to H^i(K'_{x̄'}). -/
@[stacks 0DKF] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pointCohomologyMap :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (xbar' : GeometricPoint X') (i : ℤ),
    (ModuleCat.extendScalars (pointTensorMap g' f' f g h_comm xbar').hom).obj
        (pointBaseChangeHomology g' f' f g h_comm K xbar' i) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat (etaleLocalRing X' xbar')) i).obj
        (ModuleDerived.stalkDerived xbar' ((inclusion X').obj K')))
