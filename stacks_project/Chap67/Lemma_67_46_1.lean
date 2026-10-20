/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

/- Lemma 67.46.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is finite locally free in the
sense of Section 67.3 if and only if `f` is affine and the sheaf `f_* 𝒪_X` is a
finite locally free `𝒪_Y`-module. -/
@[stacks 03ZU] #check
  (AlgebraicGeometry.AlgebraicSpace.finiteLocallyFree_presheaf_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
      yoneda.relativelyRepresentable f →
        ((over (@AlgebraicGeometry.IsFiniteLocallyFree :
          MorphismProperty Scheme.{u})).presheaf f ↔
          AlgebraicGeometry.AlgebraicSpace.Affine f ∧
            SheafOfModules.IsFiniteLocallyFree
              (AlgebraicGeometry.AlgebraicSpace.Modules.pushforwardStructureModule f)))
