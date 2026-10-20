/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Approximation of integral morphisms

This file records limit presentations of integral scheme morphisms by finite morphisms of finite
presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.IsIntegralHom

/-- An integral morphism over a quasi-compact and quasi-separated scheme is the limit, over the
target, of a nonempty directed inverse system of finite morphisms of finite presentation. -/
theorem existsFinitePresentationLimit
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegralHom f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : OrderDual I ⥤ Over S)
      (π : (Functor.const (OrderDual I)).obj (Over.mk f) ⟶ D),
      Nonempty (IsLimit (⟨Over.mk f, π⟩ : Cone D)) ∧
        ∀ j : I,
          IsFinite (D.obj j).hom ∧ Scheme.Hom.FinitePresentation (D.obj j).hom := sorry

end AlgebraicGeometry.IsIntegralHom
