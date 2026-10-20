/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalHom

/-!
# Infinitesimal composition on morphisms of lifts

Relative infinitesimal automorphisms act by composition on morphisms of lifts.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver

universe u

#check (AlgebraicGeometry.GroupoidsOver.infHomComp :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
    {x : X.p.Fiber (Over.mk σA)} (x' x'' : liftCat x fA hfA)
    (α : infinitesimalAut x') (φ : x' ⟶ x'') (β : infinitesimalAut x''),
    x' ⟶ x'')
