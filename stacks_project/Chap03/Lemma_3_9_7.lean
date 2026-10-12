/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Size
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 3.9.7. If `f : X ⟶ S` is locally of finite type and `X` is quasi-compact, then
`X.size ≤ S.size`. -/
@[stacks 04T7] #check (AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [CompactSpace X],
    X.size ≤ S.size)
