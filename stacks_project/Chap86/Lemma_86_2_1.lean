/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dualizing.EtaleLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Lemma 86.2.1: for a locally Noetherian algebraic space over a scheme, dualizingness
on every étale scheme chart is equivalent to dualizingness on one surjective étale
scheme chart. -/
@[stacks 0E4Y] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isDualizingOnScheme_forall_iff_exists :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      (K : DerivedQCoh X), forallEtaleScheme K ↔ existsSurjectiveEtaleScheme K)
