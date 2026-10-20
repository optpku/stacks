/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Endomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberRank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Reconstruction from internal endomorphism algebras

This file records the tensor-invertible ambiguity of finite locally free scheme modules with
isomorphic internal endomorphism algebras.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Positive-rank finite locally free scheme modules with isomorphic internal endomorphism
algebras differ by tensoring with an invertible scheme module. -/
theorem exists_invertible_tensorIso_of_internalEndAlgebraIso
    {S : Scheme.{u}} (F G : S.Modules)
    [IsFiniteLocallyFree F] [IsFiniteLocallyFree G]
    (hF : ∀ x : S, 0 < (fiberFinrank F x : ℕ∞))
    (hG : ∀ x : S, 0 < (fiberFinrank G x : ℕ∞))
    (h : internalHom F F ≅ internalHom G G)
    (h_id : MonoidalClosed.id F ≫ h.hom = MonoidalClosed.id G)
    (h_mul :
      (h.hom ⊗ₘ h.hom) ≫ MonoidalClosed.comp G G G =
        MonoidalClosed.comp F F F ≫ h.hom) :
    ∃ L : S.Modules, Invertible L ∧
      ∃ e : F ⊗ L ≅ G, h.hom = tensorEndMap F L ≫ (conjEndIso e).hom := sorry

end AlgebraicGeometry.Scheme.Modules
