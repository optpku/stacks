/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.17.2: For an open immersion of algebraic spaces over a scheme, the
scheme-theoretic closure of every étale preimage equals its ambient space if and only if
this holds after one surjective étale morphism from a scheme. -/
@[stacks 0833] #check (AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticDensity.tfae :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X)
    [AlgebraicSpace.IsOpenImmersion ι],
    List.TFAE [AlgebraicSpace.SchemeTheoreticDensity.forallEtale ι,
      AlgebraicSpace.SchemeTheoreticDensity.existsSurjectiveEtale ι])
