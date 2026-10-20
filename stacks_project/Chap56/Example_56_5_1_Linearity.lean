/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Linearity

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.Modules.baseLinear :
  ∀ {R : Type u} [CommRing R] {X : Scheme.{u}},
    (X ⟶ Spec (CommRingCat.of R)) → Linear R X.Modules)

#check (AlgebraicGeometry.Scheme.QCoh.LinearOver :
  ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
    (X ⟶ Spec (CommRingCat.of R)) → (Y ⟶ Spec (CommRingCat.of R)) →
    (Scheme.QCoh X ⥤ Scheme.QCoh Y) → Prop)
