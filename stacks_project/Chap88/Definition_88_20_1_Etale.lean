/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap80.Lemma_80_4_6

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale

/-!
# Étale morphisms of functors of points

A morphism of functors of points on schemes over `S` is étale when it is
representable by algebraic spaces and every Yoneda pullback is an étale
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.Etale :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop)
