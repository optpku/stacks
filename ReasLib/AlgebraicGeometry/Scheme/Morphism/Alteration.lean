/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Alterations of Integral Schemes

This leaf owns the standard proper, dominant, generically finite morphism
property between integral schemes.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- An alteration is a proper dominant morphism of integral schemes that is
finite over some nonempty open subset of the target. -/
class IsAlteration (f : Y ⟶ X) : Prop extends IsProper f, IsDominant f where
  /-- The alteration is finite on some nonempty open subset of the target. -/
  exists_nonempty_open_isFinite :
    ∃ U : X.Opens, Nonempty U ∧ IsFinite (f ∣_ U)

/-- Unfold an alteration into properness, dominance, and generic finiteness. -/
theorem isAlteration_iff (f : Y ⟶ X) :
    IsAlteration f ↔
      IsProper f ∧
        IsDominant f ∧
        ∃ U : X.Opens, Nonempty U ∧ IsFinite (f ∣_ U) := sorry

end

end AlgebraicGeometry
