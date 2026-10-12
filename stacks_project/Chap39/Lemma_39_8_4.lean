/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Smooth

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 39.8.4: over a perfect field of prime characteristic, a reduced locally algebraic
group scheme has smooth structure morphism. -/
@[stacks 047P] #check
  (AlgebraicGeometry.GroupScheme.instSmoothOfPerfectFieldOfIsReduced :
    ∀ {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectField k]
      (G : SchemeOverField k) [GrpObj G] [LocallyAlgebraic G] [IsReduced G.left], Smooth G.hom)
