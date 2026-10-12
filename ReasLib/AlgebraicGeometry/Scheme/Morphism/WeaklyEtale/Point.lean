/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.FieldTheory.IsSepClosed

open AlgebraicGeometry CategoryTheory Scheme

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme

/-- A point of a weakly étale morphism above a separably closed field-valued point
extends to a factorization of that field-valued point through the morphism. -/
theorem exists_fac_of_weaklyEtale_of_isSepClosed {X S : Scheme.{u}} (f : X ⟶ S)
    [WeaklyEtale f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : X) (hx : f x = s default) :
    ∃ (l : Spec (.of Ω) ⟶ X), l ≫ f = s ∧ l default = x := sorry

end AlgebraicGeometry.Scheme
