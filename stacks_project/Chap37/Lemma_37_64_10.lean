/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Reduced
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.64.10: if `f : X ⟶ Y` is weakly étale and `Y` is reduced, then `X` is
reduced. -/
@[stacks 094Y] #check (AlgebraicGeometry.WeaklyEtale.isReduced :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f] [IsReduced Y], IsReduced X)
