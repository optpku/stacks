/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Monoidal.Tor

@[expose] public section

open CategoryTheory

universe u

namespace LinearMap

/-- A map from a finitely presented module whose induced first Tor maps all vanish factors through
a free module presented as a finitely supported function module. -/
theorem exists_free_factorisation_of_torOne_map_eq_zero
    {R M M' : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module.FinitePresentation R M]
    (f : M →ₗ[R] M')
    (hTor : ∀ N : ModuleCat.{u} R,
      ((CategoryTheory.Tor (ModuleCat.{u} R) 1).map (ModuleCat.ofHom f)).app N = 0) :
    ∃ (ι : Type u) (toFree : M →ₗ[R] (ι →₀ R))
      (fromFree : (ι →₀ R) →ₗ[R] M'),
      fromFree.comp toFree = f := sorry

end LinearMap
