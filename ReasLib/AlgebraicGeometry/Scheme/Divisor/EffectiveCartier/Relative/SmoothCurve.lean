/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# Relative effective Cartier divisors on smooth relative curves

This file compares relative effective Cartier divisors on smooth relative curves with finiteness
and flatness properties of their structure morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace IsRelativeEffectiveCartierDivisor

/-- On a smooth relative curve, a closed subscheme is a relative effective Cartier divisor
exactly when its structure morphism is locally quasi-finite, flat, and locally of finite
presentation. -/
theorem iff_locallyQuasiFinite_flat_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (D : X.IdealSheafData) :
    IsRelativeEffectiveCartierDivisor f D ↔
      LocallyQuasiFinite (D.subschemeι ≫ f) ∧ Flat (D.subschemeι ≫ f) ∧
        LocallyOfFinitePresentation (D.subschemeι ≫ f) := sorry

/-- A finite locally free closed subscheme of a smooth relative curve is a relative effective
Cartier divisor. -/
theorem of_isFiniteLocallyFree
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (D : X.IdealSheafData) :
    IsFiniteLocallyFree (D.subschemeι ≫ f) → IsRelativeEffectiveCartierDivisor f D := sorry

end IsRelativeEffectiveCartierDivisor

/-- For a closed subscheme of a smooth relative curve, local quasi-finiteness, flatness, and
local finite presentation imply local finite type, local quasi-finiteness, and flatness. -/
theorem locallyQuasiFinite_flat_of_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (D : X.IdealSheafData) :
    LocallyQuasiFinite (D.subschemeι ≫ f) ∧ Flat (D.subschemeι ≫ f) ∧
        LocallyOfFinitePresentation (D.subschemeι ≫ f) →
      LocallyOfFiniteType (D.subschemeι ≫ f) ∧ LocallyQuasiFinite (D.subschemeι ≫ f) ∧
        Flat (D.subschemeι ≫ f) := sorry

namespace LocallyQuasiFinite

/-- Over a locally Noetherian base, local finite type, local quasi-finiteness, and flatness of a
closed subscheme of a smooth relative curve are equivalent to local quasi-finiteness, flatness,
and local finite presentation. -/
theorem flat_iff_flat_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    [IsLocallyNoetherian S] (D : X.IdealSheafData) :
    (LocallyOfFiniteType (D.subschemeι ≫ f) ∧ LocallyQuasiFinite (D.subschemeι ≫ f) ∧
      Flat (D.subschemeι ≫ f)) ↔
      LocallyQuasiFinite (D.subschemeι ≫ f) ∧ Flat (D.subschemeι ≫ f) ∧
        LocallyOfFinitePresentation (D.subschemeι ≫ f) := sorry

end LocallyQuasiFinite

/-- When a smooth relative curve is proper over the base, its finite locally free closed
subschemes are exactly its relative effective Cartier divisors. -/
theorem isFiniteLocallyFree_iff_isRelativeEffectiveCartierDivisor_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] [IsProper f]
    (D : X.IdealSheafData) :
    IsFiniteLocallyFree (D.subschemeι ≫ f) ↔ IsRelativeEffectiveCartierDivisor f D := sorry

end AlgebraicGeometry
