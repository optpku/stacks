/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Geometrically Reduced Algebras Over Perfect Fields

Reduced commutative algebras over a perfect field are geometrically reduced,
independently of any separable-generation presentation of a field extension.
-/

@[expose] public section

universe u v

namespace Algebra.IsGeometricallyReduced

/-- Over a perfect field, every reduced commutative algebra is geometrically
reduced. -/
@[stacks 00I4]
theorem of_perfectField
    {k : Type u} {R : Type v}
    [Field k] [PerfectField k] [CommRing R] [Algebra k R] [IsReduced R] :
    Algebra.IsGeometricallyReduced k R := sorry

end Algebra.IsGeometricallyReduced
