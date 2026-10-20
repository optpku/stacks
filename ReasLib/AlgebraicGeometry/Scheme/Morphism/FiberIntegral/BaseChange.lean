/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberIntegral

/-!
# Fibre integrals and base change

This module establishes preservation of finite point fibres and compatibility
of separable-degree-weighted fibre integrals with cartesian base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Finite point fibres are preserved by a cartesian base-change square whose
original vertical morphism is locally quasi-finite. -/
theorem tendstoCofinite_of_isPullback
    {U U' V V' : Scheme.{u}} {h : U' ⟶ U} {π' : U' ⟶ V'} {π : U ⟶ V} {g : V' ⟶ V}
    [LocallyQuasiFinite π] (sq : IsPullback h π' π g)
    (hπ : Filter.TendstoCofinite (fun u : U ↦ π u)) :
    Filter.TendstoCofinite (fun u' : U' ↦ π' u') := sorry

/-- The separable-degree-weighted fibre integral of an integer-valued function
commutes with base change along a cartesian square. -/
theorem fiberIntegral_baseChange
    {U U' V V' : Scheme.{u}} (π : U ⟶ V) (h : U' ⟶ U) (π' : U' ⟶ V') (g : V' ⟶ V)
    [LocallyQuasiFinite π] [hπ : Filter.TendstoCofinite (fun u : U ↦ π u)]
    (sq : IsPullback h π' π g) (w : U → ℤ) :
    (fun v' : V' ↦ π.fiberIntegral hπ w (g v')) =
      π'.fiberIntegral (tendstoCofinite_of_isPullback sq hπ) (fun u' ↦ w (h u')) := sorry

end AlgebraicGeometry.Scheme.Hom
