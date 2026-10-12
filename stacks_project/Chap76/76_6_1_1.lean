/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.«76_6_1_1_Piece»

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/-- 76.6.1.1: for an immersion of algebraic spaces, the degree-`n` piece
`C_{Z/X, n}` of the conormal algebra is characterized by the canonical
closed-immersion identification
`(liftCoborder i)_* C_{Z/X, n} ≅ I^n / I^{n+1}` on the coborder `X \ ∂Z`,
as the adjunction unit `I^n / I^{n+1} ⟶ (liftCoborder i)_* C_{Z/X, n}`. -/
@[stacks 09RP, instance]
theorem piece_pushforward (n : ℕ) :
    IsIso (piecePushforwardComparison i n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra
