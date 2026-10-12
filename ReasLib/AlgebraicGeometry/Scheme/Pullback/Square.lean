/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pullback

variable {X T S : Scheme.{u}}

/-- The canonical projections from a pullback of schemes form a pullback square. -/
theorem isPullback (f : X ⟶ S) (g : T ⟶ S) :
    IsPullback (pullback.fst f g) (pullback.snd f g) f g := sorry

end AlgebraicGeometry.Scheme.Pullback
