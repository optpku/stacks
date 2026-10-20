/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Ampleness in inverse limits of schemes

This file records the descent of ampleness for invertible modules along directed inverse limits
with affine transition morphisms.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If the pullback of an invertible module from one stage of a directed inverse system of
quasi-compact and quasi-separated schemes with affine transition morphisms is ample on the
limit, then its pullback is ample on some upper stage. -/
theorem exists_stage_isAmple_pullback_of_isAmple_limit_pullback
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i₀ : I) (ℒ₀ : (D.obj i₀).Modules) [Invertible ℒ₀]
    [IsAmple ((Scheme.Modules.pullback (c.π.app i₀)).obj ℒ₀)] :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsAmple ((Scheme.Modules.pullback (D.map (homOfLE hi))).obj ℒ₀) := sorry

end AlgebraicGeometry.Scheme.Modules
