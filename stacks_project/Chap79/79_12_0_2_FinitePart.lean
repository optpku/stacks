/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Logic.Small.Defs
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Remark_67_12_5_Opens

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Opens

/-! # Points-open presentation of the finite-part presheaf -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits Opposite
universe u

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Over S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.of :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    (a : ofOver T ⟶ Y) (Z : TopologicalSpace.Opens (Points (pullback a f))),
    IsFinite ((OpenSubspace.fromOpens Z).ι ≫ pullback.fst a f) → FinitePart.Point f T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S}
    (p : FinitePart.Point f T),
    IsOpenImmersion (OpenSubspace.fromOpens p.Z).ι ∧ IsFinite p.pr0)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.restrict :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {T T' : Over S},
    FinitePart.Point f T → (T' ⟶ T) → FinitePart.Point f T')

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.pointsFunctor :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → (Over S)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.pointsFunctor_obj_equiv :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (T : Over S),
    (FinitePart.pointsFunctor f).obj (op T) ≃ FinitePart.Point f T)
