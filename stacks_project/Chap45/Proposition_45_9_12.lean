/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Correspondence

@[expose] public section

universe u v

/- Proposition 45.9.12 -/
@[stacks 0FHM]
#check (WeilCohomology.classicalTheoryCorrespondence :
    ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F],
      Nonempty
        (WeilCohomology.SchemeClassicalTheory.Object k F ≃
          WeilCohomology.MotivicRealization.Admissible k F))
