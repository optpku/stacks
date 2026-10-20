/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Groupoids

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 99.5.2: in Situation 99.5.1 the projection from coherent sheaves on
`X/B` to schemes over `S` is fibred in groupoids. -/
@[stacks 08W5] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.instIsFiberedInGroupoids :
  ∀ {S : Scheme.{u}} {X B : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ B),
    [AlgebraicGeometry.AlgebraicSpace.FinitePresentation f] →
      CategoryTheory.Functor.IsFibered.InGroupoids
        (AlgebraicGeometry.AlgebraicSpace.CohStack.p f))

