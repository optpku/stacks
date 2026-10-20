/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Definition 71.14.1: Let S be a scheme. Let f : X ⟶ Y be a morphism of algebraic
spaces over S. Let L be an invertible 𝒪_X-module. We say L is relatively ample, or
f-relatively ample, or ample on X/Y, or f-ample if f is representable and, for every
morphism Z ⟶ Y with Z a scheme, the pullback of L to X_Z = Z ×_Y X is relatively
ample on X_Z/Z in the sense of AlgebraicGeometry.RelativelyAmple. -/
@[stacks 0D31] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → X.Modules → Prop)

#check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules),
      AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L ↔
        yoneda.relativelyRepresentable f ∧
          ∀ {Z W : Over S} {g : ofOver Z ⟶ Y} {pX : ofOver W ⟶ X} {pZ : W ⟶ Z},
            IsPullback pX (ofOverMap pZ) f g →
              AlgebraicGeometry.RelativelyAmple pZ.left
                ((Modules.restrictToScheme W).obj ((Modules.pullback pX).obj L)))
