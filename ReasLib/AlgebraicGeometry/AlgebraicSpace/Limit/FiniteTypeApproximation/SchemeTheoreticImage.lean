/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.IsLimit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation.Diagram
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.BaseChange

/-!
# Scheme-theoretic images in finite-type approximation systems

A compatible inverse system of scheme-theoretic images of a quasi-separated
finite-type algebraic space, taken in the base changes of a good finite-type
approximation square, has that space as its limit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram

/-- The canonical cone from the source algebraic space to the stagewise base
changes determined by a finite-type approximation diagram. -/
noncomputable def baseChangeCone {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) {i : I}
    {X : AlgebraicSpace S} {f : X ⟶ c.pt}
    (approximation : FiniteTypeApproximationDiagram f (c.π.app i)) :
    Cone (baseChangeOverDiagram D (OrderDual.toDual i) approximation.toBi) :=
  (baseChangeOverCone D c (OrderDual.toDual i) approximation.toBi).extend
    (pullback.lift f approximation.toW approximation.comm.w.symm)

/-- The vertex of `baseChangeCone` is the source algebraic space. -/
theorem baseChangeCone_pt {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) {i : I}
    {X : AlgebraicSpace S} {f : X ⟶ c.pt}
    (approximation : FiniteTypeApproximationDiagram f (c.π.app i)) :
    (approximation.baseChangeCone D c).pt = X :=
  sorry

/-- A compatible tail system of scheme-theoretic images of a quasi-separated
finite-type algebraic space in the base changes of a Noetherian inverse system
has that space as its limit. -/
theorem nonempty_isLimit_schemeTheoreticImageCone
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (i : I) {X : AlgebraicSpace S} (f : X ⟶ c.pt)
    [QuasiSeparated f] [FiniteType f]
    (approximation : FiniteTypeApproximationDiagram f (c.π.app i))
    [FiniteType approximation.toBi]
    [IsClosedImmersion
      (pullback.lift f approximation.toW approximation.comm.w.symm)]
    (Xi : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S)
    (π : (Functor.const (Over (OrderDual.toDual i))).obj X ⟶ Xi)
    (ι : Xi ⟶ baseChangeOverDiagram D (OrderDual.toDual i) approximation.toBi)
    (himage : ∀ j, IsSchemeTheoreticImage
      ((approximation.baseChangeCone D c).π.app j) (π.app j) (ι.app j)) :
    Nonempty (IsLimit (⟨X, π⟩ : Cone Xi)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram
