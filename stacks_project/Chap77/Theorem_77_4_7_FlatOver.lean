/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import stacks_project.Chap66.Definition_66_18_9_Square
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap66.Proposition_66_32_1_Comparison

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# Relative flatness of modules on algebraic spaces

The canonical chart restriction defines relative flatness at a point and
provides its étale-chart criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
    X.Modules → (X ⟶ Y) → Points X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    (x : Points X),
    flatOverAt F f x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
        (ha : Etale a) (hb : Etale b),
        a ≫ f = ofOverMap h ≫ b ∧
          Points.map a (ofOver.pointsEquiv U u) = x ∧
            Scheme.Modules.flatOverAt
              ((@restrictFunctor S (ofOver U) X a ha ⋙ restrictToScheme U).obj F) h.left u)
