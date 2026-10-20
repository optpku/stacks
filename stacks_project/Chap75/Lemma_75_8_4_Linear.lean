/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Linearity

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.globalSectionsMap :
  ∀ {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))),
    A →+* globalSectionsRing X)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.baseLinear :
  ∀ {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))),
    Linear A (Modules X))
