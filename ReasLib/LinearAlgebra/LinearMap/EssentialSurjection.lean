/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Submodule.Range

@[expose] public section

universe u v w

/-- A linear map is an essential surjection if it is surjective and no proper submodule of
its domain maps onto its codomain. -/
def LinearMap.IsEssentialSurjection
    {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M] (f : P →ₗ[R] M) : Prop :=
  f.range = ⊤ ∧ ∀ N : Submodule R P, N.map f = ⊤ → N = ⊤

namespace LinearMap.IsEssentialSurjection

/-- Construct an essential surjection from its surjectivity and submodule-minimality
conditions. -/
def of {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M] {f : P →ₗ[R] M}
    (range_eq_top : f.range = ⊤)
    (eq_top_of_map_eq_top : ∀ N : Submodule R P, N.map f = ⊤ → N = ⊤) :
    f.IsEssentialSurjection :=
  ⟨range_eq_top, eq_top_of_map_eq_top⟩

/-- An essential surjection is equivalently a surjective map for which every submodule
mapping onto the codomain is the whole domain. -/
theorem iff_range_eq_top
    {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M] {f : P →ₗ[R] M} :
    f.IsEssentialSurjection ↔
      f.range = ⊤ ∧ ∀ N : Submodule R P, N.map f = ⊤ → N = ⊤ := sorry

end LinearMap.IsEssentialSurjection
