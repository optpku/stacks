/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Kaehler.Basic

@[expose] public section

open scoped TensorProduct

universe u v

namespace KaehlerDifferential

/-- The Noether different of a commutative algebra, defined as the image under multiplication
of the annihilator of the diagonal ideal. -/
noncomputable def noetherDifferent (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] :
    Ideal B :=
  Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom (ideal A B).annihilator

/-- The Noether different is the image of the annihilator of the diagonal ideal under
multiplication. -/
theorem noetherDifferent_eq_map (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] :
    noetherDifferent A B =
      Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom (ideal A B).annihilator := sorry

/-- Membership in the Noether different is witnessed by an annihilating tensor whose
product is the given element. -/
theorem mem_noetherDifferent (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (b : B) :
    b ∈ noetherDifferent A B ↔
      ∃ ξ : B ⊗[A] B, ξ ∈ (ideal A B).annihilator ∧
        Algebra.TensorProduct.lmul' A ξ = b := sorry

end KaehlerDifferential
