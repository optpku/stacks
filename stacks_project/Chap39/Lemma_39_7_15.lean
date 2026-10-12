/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.CountableAffineOpen
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

/- Lemma 39.7.15: Every group scheme over a field contains the identity point in a clopen
open subscheme that is a countable union of affine opens. -/
@[stacks 047U] #check
  (AlgebraicGeometry.GroupScheme.existsClopenCountableAffineCover :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G],
      ∃ U : G.left.Opens,
        η[G].left (IsLocalRing.closedPoint k) ∈ (U : Set G.left) ∧
          IsClopen (U : Set G.left) ∧
            ∃ V : ℕ → G.left.Opens, (∀ n, IsAffineOpen (V n)) ∧ iSup V = U)
