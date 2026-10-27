/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap97.Lemma_97_11_4_RelativeHom
public import stacks_project.Chap99.Lemma_99_7_5_SpacePoint

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Sheaf

/-!
# Quotient sheaves on schemes over the base

The quotient sheaves and their canonical comparison maps are imported from their
mathematical owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Quot.toSheafHom :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent] (T : AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.Quot.SpaceQuotient f F T →
      (AlgebraicSpace.toSheaf.obj T ⟶ AlgebraicGeometry.AlgebraicSpace.Quot.sheaf f F))

#check (AlgebraicGeometry.AlgebraicSpace.Quot.toFpSheafHom :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent] (T : AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.Quot.FpSpaceQuotient f F T →
      (AlgebraicSpace.toSheaf.obj T ⟶ AlgebraicGeometry.AlgebraicSpace.Quot.fpSheaf f F))
