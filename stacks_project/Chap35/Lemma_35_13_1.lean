/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Pullback.Point
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 35.13.1: for a scheme morphism `f : X ⟶ S`, the canonical map
from the points of `X ×_S X` to the pullback of `|X|` over `|S|` is surjective. -/
@[stacks 02KI] #check
  (AlgebraicGeometry.Scheme.pullbackComparison_forget_self_surjective :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Function.Surjective (pullbackComparison Scheme.forget f f))
