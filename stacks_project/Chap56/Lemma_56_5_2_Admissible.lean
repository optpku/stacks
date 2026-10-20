/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Admissible

@[expose] public section

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

/- The admissible-functor API is owned by the reusable quasicoherent-module library. -/
#check (AlgebraicGeometry.Scheme.QCoh.Admissible :
  ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
    (X ⟶ Spec (CommRingCat.of R)) →
    (Y ⟶ Spec (CommRingCat.of R)) →
    (Scheme.QCoh X ⥤ Scheme.QCoh Y) → Prop)
#check (AlgebraicGeometry.Scheme.QCoh.admissible_iff :
  ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
    (x : X ⟶ Spec (CommRingCat.of R)) →
    (y : Y ⟶ Spec (CommRingCat.of R)) →
    (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) →
    (AlgebraicGeometry.Scheme.QCoh.Admissible x y F ↔
      AlgebraicGeometry.Scheme.QCoh.LinearOver x y F ∧
        rightExactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F ∧
          ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F))
#check (AlgebraicGeometry.Scheme.QCoh.RightExactCoproductLinearFunctor :
  ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
    (X ⟶ Spec (CommRingCat.of R)) →
    (Y ⟶ Spec (CommRingCat.of R)) →
    Type (u + 1))
#check (AlgebraicGeometry.Scheme.QCoh.functorCategory_property :
  ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
    (x : X ⟶ Spec (CommRingCat.of R)) →
    (y : Y ⟶ Spec (CommRingCat.of R)) →
    (F : AlgebraicGeometry.Scheme.QCoh.RightExactCoproductLinearFunctor x y) →
    AlgebraicGeometry.Scheme.QCoh.Admissible x y F.obj)
