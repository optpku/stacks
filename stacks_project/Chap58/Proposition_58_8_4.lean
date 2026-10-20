/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.UniversalHomeomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
universe u

/- Proposition 58.8.4 (1): for a universal homeomorphism, finite étale base
change is an equivalence. -/
@[stacks 0BQN] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChangeIsEquivalenceOfUniversalHomeomorphism :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f],
      Functor.IsEquivalence (Scheme.finiteEtaleBaseChange f))

/- Proposition 58.8.4 (2): for connected schemes, a universal homeomorphism
induces an isomorphism on étale fundamental groups at a geometric point. -/
@[stacks 0BQN] #check
  (AlgebraicGeometry.Scheme.fundamentalGroupIso_of_universalHomeomorphism :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f]
      [ConnectedSpace X] [ConnectedSpace Y]
      {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      IsHomeomorph (AlgebraicGeometry.Scheme.Hom.fundamentalGroupMap f s))
