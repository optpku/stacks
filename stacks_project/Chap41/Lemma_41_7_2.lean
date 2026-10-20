/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Proper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 41.7.2: A scheme morphism is a closed immersion exactly when it satisfies
any of the six equivalent combinations of properness or universal closedness with
monomorphism, unramifiedness, universal injectivity, local finite type, and formal
unramifiedness listed below. -/
@[stacks 04XV] #check
  (AlgebraicGeometry.IsClosedImmersion.tfae :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      List.TFAE
        [ IsClosedImmersion f
        , IsProper f ∧ Mono f
        , IsProper f ∧ Unramified f ∧ UniversallyInjective f
        , UniversallyClosed f ∧ Unramified f ∧ Mono f
        , UniversallyClosed f ∧ Unramified f ∧ UniversallyInjective f
        , UniversallyClosed f ∧ LocallyOfFiniteType f ∧ Mono f
        , UniversallyClosed f ∧ UniversallyInjective f ∧ LocallyOfFiniteType f ∧
            FormallyUnramified f ])
