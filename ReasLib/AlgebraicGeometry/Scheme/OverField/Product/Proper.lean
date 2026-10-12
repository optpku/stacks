/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Proper projections from products over a field

This file records properness of a product projection when the opposite factor is proper over
the base field.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The first projection from a product over a field is proper when the second factor is
proper over the field. -/
theorem prodFstIsProper (X Y : SchemeOverField k) [IsProper Y.hom] :
    IsProper (Over.Hom.left (prod.fst : X ⨯ Y ⟶ X)) := sorry

end AlgebraicGeometry.SchemeOverField
