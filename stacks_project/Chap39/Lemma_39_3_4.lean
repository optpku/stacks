/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Point
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/- Lemma 39.3.4: if a pre-relation on `U` over `S` induces an equivalence relation on
`T/S`-valued points for every `T : Over S`, then it induces an equivalence relation on the
underlying points of `U.left`. -/
@[stacks 022Q] #check
  (AlgebraicGeometry.Scheme.PreRelation.pointRelIsEquivalence :
    ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U), P.IsPreEquivalence →
      Equivalence (fun x y : U.left ↦
        ∃ r : P.left.left, P.t.left r = x ∧ P.s.left r = y))

end AlgebraicGeometry.Scheme.PreRelation
