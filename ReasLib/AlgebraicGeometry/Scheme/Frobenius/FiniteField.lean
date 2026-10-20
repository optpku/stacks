/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Finite.GaloisField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Characteristic
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Geometric

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

/-- A scheme over a field of characteristic `p` has characteristic `p`. -/
instance instIsCharP (X : SchemeOverField k) : Scheme.IsCharP X.left p :=
  isCharP_of_target X.hom

/-- The exponent `f` such that `#k = p ^ f`. -/
def finiteFieldRank (k : Type u) [Field k] [Fintype k] (p : ℕ) [Fact p.Prime]
    [CharP k p] [Algebra (ZMod p) k] : ℕ :=
  Module.finrank (ZMod p) k

/-- Geometric Frobenius of `X / k` with the canonical exponent `Module.finrank (ZMod p) k`. -/
abbrev geometricFrobenius_ofFiniteField [Fintype k] (X : SchemeOverField k) : X.left ⟶ X.left :=
  geometricFrobenius p (finiteFieldRank k p) X

/-- Geometric Frobenius over `k` with the canonical finite-field exponent. -/
abbrev geometricFrobeniusOver_ofFiniteField [Fintype k] (X : SchemeOverField k) : X ⟶ X :=
  geometricFrobeniusOver p (finiteFieldRank k p)
    (FiniteField.pow_finrank_eq_card p k).symm X

end AlgebraicGeometry.SchemeOverField
