/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.ResidueField
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

/-- If all points of the base are closed, all points of a weakly étale scheme
over it are closed. -/
theorem isClosed_singleton_of_weaklyEtale {X Y : Scheme.{u}} (f : Y ⟶ X)
    [WeaklyEtale f] (h_closed : ∀ x : X, IsClosed ({x} : Set X)) (y : Y) :
    IsClosed ({y} : Set Y) :=
  sorry

/-- If the residue fields of the base are separably closed, the residue fields
of a weakly étale scheme over it are separably closed. -/
theorem isSepClosed_residueField_of_weaklyEtale {X Y : Scheme.{u}} (f : Y ⟶ X)
    [WeaklyEtale f] (h_res : ∀ x : X, IsSepClosed (X.residueField x)) (y : Y) :
    IsSepClosed (Y.residueField y) :=
  sorry

end AlgebraicGeometry.Scheme
