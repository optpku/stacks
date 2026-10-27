/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap99.«99_7_1_1_Functor»
public import stacks_project.Chap99.«99_7_1_2_Functor»

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.SpacePoint

/-!
# Quotient points over algebraic spaces

The quotient-point API is imported from its mathematical owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Quot.SpacePoint.ofEpi :
  ∀ {S : Scheme.{u}} {X B T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) (module : (CategoryTheory.Limits.pullback f h).Modules)
    (map : AlgebraicGeometry.AlgebraicSpace.Quot.spaceFiberF f F h ⟶ module),
    Epi map → module.IsQuasicoherent →
      Modules.flatOver module (CategoryTheory.Limits.pullback.snd f h) →
        AlgebraicGeometry.AlgebraicSpace.Quot.SpacePoint f F h)
