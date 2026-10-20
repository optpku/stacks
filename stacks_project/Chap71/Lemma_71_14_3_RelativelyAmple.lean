/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative

/-!
# Relatively ample modules on algebraic spaces

An invertible module on an algebraic space is relatively ample for a morphism when
that morphism is representable and every scheme base change is relatively ample in
the sense of schemes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → X.Modules → Prop)

#check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules),
      RelativelyAmple f L ↔
        yoneda.relativelyRepresentable f ∧
          ∀ {Z W : Over S} {g : ofOver Z ⟶ Y} {pX : ofOver W ⟶ X} {pZ : W ⟶ Z},
            IsPullback pX (ofOverMap pZ) f g →
              AlgebraicGeometry.RelativelyAmple pZ.left
                ((Modules.restrictToScheme W).obj ((Modules.pullback pX).obj L)))

#check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.ofOverMap :
    ∀ {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) (L : (ofOver U).Modules)
      [AlgebraicGeometry.RelativelyAmple h.left ((Modules.restrictToScheme U).obj L)],
      RelativelyAmple (ofOverMap h) L)

end AlgebraicGeometry.AlgebraicSpace
