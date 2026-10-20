/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Finite approximation of algebraic spaces

Finite morphisms to quasi-compact, quasi-separated algebraic spaces admit directed
inverse-limit presentations by finite morphisms of finite presentation with
closed-immersion transition maps.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Diagram data form a finite approximation of a morphism when the cone with
vertex its source is limiting, its legs recover the morphism over the target,
the transition maps are closed immersions, and the stage maps are finite and
of finite presentation. -/
def IsFiniteApproximation {S : Scheme.{u}} {I : Type u} [Preorder I]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (D : OrderDual I ⥤ AlgebraicSpace S)
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : D ⟶ (Functor.const (OrderDual I)).obj Y) : Prop :=
  Nonempty (IsLimit (Cone.mk X π)) ∧
    (∀ i, π.app i ≫ σ.app i = f) ∧
    (∀ {i j : I} (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h))) ∧
    (∀ i, IsFinite (σ.app i)) ∧
    ∀ i, FinitePresentation (σ.app i)

/-- A finite approximation is equivalently a limiting cone recovering the given
morphism over the target, with closed-immersion transitions and finite stage
maps of finite presentation. -/
theorem isFiniteApproximation_iff {S : Scheme.{u}} {I : Type u} [Preorder I]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (D : OrderDual I ⥤ AlgebraicSpace S)
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : D ⟶ (Functor.const (OrderDual I)).obj Y) :
    IsFiniteApproximation f D π σ ↔
      Nonempty (IsLimit (Cone.mk X π)) ∧
        (∀ i, π.app i ≫ σ.app i = f) ∧
        (∀ {i j : I} (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h))) ∧
        (∀ i, IsFinite (σ.app i)) ∧
        ∀ i, FinitePresentation (σ.app i) :=
  Iff.rfl

/-- A finite morphism of algebraic spaces over a scheme, with quasi-compact and
absolutely quasi-separated target, admits a nonempty directed inverse-limit
presentation over that target with closed-immersion transition maps and finite
stage maps of finite presentation. -/
theorem exists_finiteApproximation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    ∃ (I : Type u) (preorderI : Preorder I) (nonemptyI : Nonempty I)
      (directedI : IsDirected I (· ≤ ·)) (D : OrderDual I ⥤ AlgebraicSpace S)
      (π : (Functor.const (OrderDual I)).obj X ⟶ D)
      (σ : D ⟶ (Functor.const (OrderDual I)).obj Y),
      IsFiniteApproximation f D π σ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
