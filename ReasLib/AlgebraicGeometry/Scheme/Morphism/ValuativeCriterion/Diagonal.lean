/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Valuative squares for diagonal morphisms

This module records the projection identities satisfied by a chosen lift of a valuative
commutative square for the diagonal of a scheme morphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ValuativeCommSq

variable {X₀ S : Scheme.{u}} {f : X₀ ⟶ S}
variable (sq : ValuativeCommSq (pullback.diagonal f))

/-- A lift of a valuative square for a diagonal, followed by the first pullback projection,
equals the lifting morphism. -/
theorem diagonalLift_comp_fst (l : sq.commSq.LiftStruct) :
    sq.i₂ ≫ pullback.fst f f = l.l := by
  calc
    sq.i₂ ≫ pullback.fst f f = (l.l ≫ pullback.diagonal f) ≫ pullback.fst f f := by
      rw [l.fac_right]
    _ = l.l := by simp [Category.assoc]

/-- A lift of a valuative square for a diagonal, followed by the second pullback projection,
equals the lifting morphism. -/
theorem diagonalLift_comp_snd (l : sq.commSq.LiftStruct) :
    sq.i₂ ≫ pullback.snd f f = l.l := by
  calc
    sq.i₂ ≫ pullback.snd f f = (l.l ≫ pullback.diagonal f) ≫ pullback.snd f f := by
      rw [l.fac_right]
    _ = l.l := by simp [Category.assoc]

end AlgebraicGeometry.ValuativeCommSq
