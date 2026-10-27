/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula.Finite
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.4.4. For a finite morphism, the canonical projection formula holds for arbitrary
unbounded derived modules over arbitrary commutative étale coefficient sheaves. -/
@[stacks 0DK5] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFinite.derivedProjectionFormula :
    ∀
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (π : X ⟶ Y) [IsFinite π]
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (B : Sheaf (smallEtaleTopology Y) CommRingCat.{u})
    (φ : (etaleRingedSite Y B).structureSheaf ⟶
      (ringPushforward π).obj (etaleRingedSite X A).structureSheaf)
    (K : EtaleDerived.category Y B) (M : EtaleDerived.category X A),
      IsIso (EtaleDerived.projectionFormula π φ K M))
