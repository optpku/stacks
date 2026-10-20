/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap72.Lemma_72_9_3
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Remark 72.9.4: this is a sketch of a proof of Lemma 72.9.3 which avoids
More on Groupoids, Lemma 40.14.10. -/
@[stacks 0ADE] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_open_isScheme_of_localRingDimAt_le_one :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelySeparated X]
      [IsLocallyNoetherian X] (x : Points X),
      localRingDimAt x ≤ 1 →
        ∃ U : OpenSubspace X, IsScheme U.X ∧ x ∈ U.pointsSet)
