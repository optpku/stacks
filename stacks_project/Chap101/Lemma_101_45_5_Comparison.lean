/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Comparison.Construction

/-!
# Inertia comparison to a fibre product

The canonical inertia comparison and its projection specifications are provided
by the reusable construction over the base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia
open AlgebraicGeometry.AlgebraicStack.Inertia
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.Inertia.comparisonCone :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    PseudoPullbackCone f (forget.{u + 1, u, u, u + 1} Y))

#check (AlgebraicGeometry.AlgebraicStack.Inertia.comparisonCone_pt :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y),
    (comparisonCone f).pt = inertia.{u + 1, u, u, u + 1} X)

#check (AlgebraicGeometry.AlgebraicStack.Inertia.comparisonCone_fst :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y),
    (comparisonCone f).fst = forget.{u + 1, u, u, u + 1} X)

#check (AlgebraicGeometry.AlgebraicStack.Inertia.comparisonCone_snd :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y),
    (comparisonCone f).snd = map.{u + 1, u, u, u + 1} f)

#check (AlgebraicGeometry.AlgebraicStack.Inertia.comparisonCone_iso :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y),
    (comparisonCone f).iso =
      eqToIso (map.comp_forget.{u + 1, u, u, u + 1} f).symm)

#check (AlgebraicGeometry.AlgebraicStack.Inertia.comparison :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    inertia.{u + 1, u, u, u + 1} X ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f
        (forget.{u + 1, u, u, u + 1} Y))

#check (AlgebraicGeometry.AlgebraicStack.Inertia.comparison_eq :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    comparison f =
      PseudoPullbackCone.lift (comparisonCone f)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f
          (forget.{u + 1, u, u, u + 1} Y)))

#check (AlgebraicGeometry.AlgebraicStack.Inertia.comparison_fstIso :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    comparison f ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} f
          (forget.{u + 1, u, u, u + 1} Y) ≅
      forget.{u + 1, u, u, u + 1} X)

#check (AlgebraicGeometry.AlgebraicStack.Inertia.comparison_sndIso :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    comparison f ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} f
          (forget.{u + 1, u, u, u + 1} Y) ≅
      map.{u + 1, u, u, u + 1} f)
