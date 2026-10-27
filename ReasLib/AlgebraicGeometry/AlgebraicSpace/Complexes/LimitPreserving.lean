/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.CategoryTheory.Fibered.Fiber.DirectedSystem

/-!
# Limit preservation of the fibration of complexes

The fibration of relatively perfect complexes with vanishing negative fibre
self-Ext has object descent and Hom-colimits along directed affine inverse
limits when its base is locally of finite presentation. Its Hom diagrams take
values in `Type (u + 1)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open CategoryTheory.Functor.Fiber

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Object descent for `p f` along directed inverse limits of affine schemes
over `S`. -/
theorem exists_stage (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (SchemeRealization.toBase B)]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (x : (p f).Fiber c.pt) :
    ∃ (i : I) (xi : (p f).Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x := sorry

/-- Fibre Hom-types of `p f` over a directed inverse limit of affine schemes
over `S` are the directed colimit of the corresponding stage Hom-types. -/
theorem hom_isColimit (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (SchemeRealization.toBase B)]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (i : I) (x y : (p f).Fiber (D.obj i)) :
    Nonempty (IsColimit (CategoryTheory.Functor.Fiber.DirectedSystem.homCocone
      (p f) c x y)) := sorry

/-- For a proper, flat morphism `f : X ⟶ B` of finite presentation with `B`
locally of finite presentation over `S`, the fibration of relatively perfect
complexes with vanishing negative fibre self-Ext has object descent and
Hom-colimits along every directed inverse limit of affine schemes over `S`. -/
theorem isLimitPreserving (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (SchemeRealization.toBase B)]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left) :
    (∀ x : (p f).Fiber c.pt, ∃ (i : I) (xi : (p f).Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
      ∀ (i : I) (x y : (p f).Fiber (D.obj i)),
        Nonempty (IsColimit (CategoryTheory.Functor.Fiber.DirectedSystem.homCocone
          (p f) c x y)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
