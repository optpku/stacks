/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Diagram
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage

/-!
# Scheme-theoretic images in finite-type approximation systems

This file records the limit property of a compatible inverse system of
scheme-theoretic images inside the base changes determined by a finite-type
approximation diagram.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/-- A compatible tail system of scheme-theoretic images of a quasi-separated finite-type
scheme in the base changes of a Noetherian inverse system has that scheme as its limit. -/
theorem nonempty_isLimit_schemeTheoreticImageCone
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) {X : Scheme.{u}} (f : X ⟶ c.pt)
    [QuasiSeparated f] [Scheme.Hom.FiniteType f]
    (approximation : FiniteTypeApproximationDiagram f (c.π.app i))
    [Scheme.Hom.FiniteType approximation.toSi]
    [IsClosedImmersion
      (pullback.lift f approximation.toW approximation.w.symm)]
    (Xi : Over (show OrderDual I from i) ⥤ Scheme.{u})
    (π : (Functor.const (Over (show OrderDual I from i))).obj X ⟶ Xi)
    (ι : Xi ⟶
      Scheme.baseChangeOverDiagram D (show OrderDual I from i) approximation.toSi)
    (himage : ∀ j : Over (show OrderDual I from i),
      IsSchemeTheoreticImageFactorization
        ((approximation.baseChangeCone D c).π.app j) (π.app j) (ι.app j)) :
    Nonempty (IsLimit (⟨X, π⟩ : Cone Xi)) := sorry

end AlgebraicGeometry.FiniteTypeApproximationDiagram
