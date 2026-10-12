/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Ring

@[expose] public section

/-!
# Geometrically normal field algebras

This module owns the intrinsic field-algebra condition that every field
base change is a normal ring. The class is the reusable API, and the explicit
universal formulation gives its field-extension criterion.
-/

open scoped TensorProduct

universe u v

namespace Algebra

/-- A commutative `k`-algebra `R` is geometrically normal over `k` when every field extension
`K / k` gives a normal tensor base change `K ⊗[k] R`. -/
@[stacks 0380]
class IsGeometricallyNormal (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] :
    Prop where
  /-- Normality after a field extension of the base. -/
  isNormalRing_baseChange (K : Type (max u v)) [Field K] [Algebra k K] :
    IsNormalRing (K ⊗[k] R)

attribute [instance] IsGeometricallyNormal.isNormalRing_baseChange

namespace IsGeometricallyNormal

/-- Geometric normality is equivalent to normality after every field-extension tensor base
change. -/
@[stacks 0380]
theorem iff_forall_isNormalRing_tensorProduct
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R] :
    IsGeometricallyNormal k R ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K], IsNormalRing (K ⊗[k] R) := sorry

end IsGeometricallyNormal

/-- The ground field is geometrically normal over itself. -/
@[stacks 0380]
instance instIsGeometricallyNormalSelf (k : Type u) [Field k] :
    IsGeometricallyNormal k k := sorry

end Algebra
