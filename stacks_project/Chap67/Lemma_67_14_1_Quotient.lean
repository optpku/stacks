/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealQuotient

/-! # Quotient of a module by an ideal action

The public owner retains actual recast maps, ideal action, cokernel and adjunction-unit descent.
The calling source lemma keeps its precise source-facing statement and tag.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.quotientByIdealComparison :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) (F : X.Modules),
    Modules.quotientByIdeal (Hom.idealSheafSubobject i) F ⟶
      (Modules.pushforward i).obj ((Modules.pullback i).obj F))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.π_comp_comparison :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) (F : X.Modules),
    Modules.quotientByIdeal.π (Hom.idealSheafSubobject i) F ≫
        Modules.quotientByIdealComparison i F =
      (Modules.pullbackPushforwardAdjunction i).unit.app F)
