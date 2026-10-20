/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap99.«99_3_1_1»

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SpaceHom

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Space-level Hom pairs of quasi-coherent modules: a base morphism and a module
morphism on its pullback determine a pair. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.SpaceHom.of :
  ∀ {S : Scheme.{u}} {X B T : AlgebraicSpace S} {f : X ⟶ B} {F G : X.Modules}
    (h : T ⟶ B),
    (AlgebraicGeometry.AlgebraicSpace.Modules.spaceBaseChangeModule f h F ⟶
      AlgebraicGeometry.AlgebraicSpace.Modules.spaceBaseChangeModule f h G) →
    AlgebraicGeometry.AlgebraicSpace.Modules.SpaceHom f F G T)
