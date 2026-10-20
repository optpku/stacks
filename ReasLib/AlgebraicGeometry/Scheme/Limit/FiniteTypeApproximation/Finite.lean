/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Finite

/-!
# Finite-stage approximations of finite morphisms

This file records directed limit presentations of finite scheme morphisms by finite,
finite-presentation stages with closed-immersion transition maps.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

namespace FiniteTypeApproximation

/-- Fixed data form a finite closed-immersion finite-presentation approximation when their cone
is limiting, their structure maps are compatible over the base and recover the original
morphism, every transition map is a closed immersion, and every stage map is finite and of
finite presentation. -/
def IsFiniteClosedImmersion {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) : Prop :=
  Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
    (∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k) ∧
    (∀ j : I, π.app j ≫ σ j = f) ∧
    (∀ {j k : I} (hjk : j ≤ k), IsClosedImmersion (D.map (homOfLE hjk))) ∧
    (∀ j : I, IsFinite (σ j)) ∧
    ∀ j : I, Scheme.Hom.FinitePresentation (σ j)

/-- A finite closed-immersion finite-presentation approximation is equivalently a limiting
compatible system over the base that recovers the original morphism and has closed-immersion
transitions and finite, finite-presentation stage maps. -/
theorem isFiniteClosedImmersion_iff
    {I : Type u} [Preorder I] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) :
    IsFiniteClosedImmersion f D π σ ↔
      Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
        (∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k) ∧
        (∀ j : I, π.app j ≫ σ j = f) ∧
        (∀ {j k : I} (hjk : j ≤ k), IsClosedImmersion (D.map (homOfLE hjk))) ∧
        (∀ j : I, IsFinite (σ j)) ∧
        ∀ j : I, Scheme.Hom.FinitePresentation (σ j) := sorry

/-- A finite morphism to a quasi-compact, quasi-separated scheme admits a directed limiting
presentation with closed-immersion transition maps and finite, finite-presentation stage maps. -/
theorem exists_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
          ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          ∃ (σ : ∀ j : I, D.obj j ⟶ S),
            IsFiniteClosedImmersion f D π σ := sorry

end FiniteTypeApproximation

end AlgebraicGeometry.Scheme.Limit
