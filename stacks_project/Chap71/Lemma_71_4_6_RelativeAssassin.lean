/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus

/-!
# Relative assassin of modules on algebraic spaces

When the fibres of `f : X ⟶ Y` are locally Noetherian, the relative assassin
`Ass_{X/Y}(F)` is the relative weak assassin of `F` in `X` over `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeWeakAss :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
    (X ⟶ Y) → X.Modules → Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_relativeWeakAss_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : X.Modules) (x : Points X),
    x ∈ relativeWeakAss f F ↔
      ∃ (p : FieldValuedPoint Y) (t : Points (fieldFiber f p)),
        Points.mk p = Points.map f x ∧
          Points.map (fieldFiberι f p) t = x ∧
            t ∈ ((pullback (fieldFiberι f p)).obj F).weakAss)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
    (X ⟶ Y) → X.Modules → Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_relativeAssassin_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : X.Modules) (x : Points X),
    x ∈ relativeAssassin f F ↔
      ∃ (p : FieldValuedPoint Y) (t : Points (fieldFiber f p)),
        Points.mk p = Points.map f x ∧
          Points.map (fieldFiberι f p) t = x ∧
            t ∈ ((pullback (fieldFiberι f p)).obj F).weakAss)
