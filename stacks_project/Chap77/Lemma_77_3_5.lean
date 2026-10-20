/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap77.Lemma_77_3_5_Purity
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.3.5 (1): a finite type quasicoherent module on a closed subspace is
pure above `y` if and only if its pushforward is pure above `y`. -/
@[stacks 0CVH] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isPureAlong_pushforward_iff_of_isClosedImmersion :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
      [Decent f] (i : Z ⟶ X) [IsClosedImmersion i]
      (G : Z.Modules) [G.IsQuasicoherent] [G.IsFiniteType] (y : Points Y),
      G.IsPureAlong (i ≫ f) y ↔
        ((pushforward i).obj G).IsPureAlong f y)

/- Lemma 77.3.5 (2): a finite type quasicoherent module on a closed subspace is
universally pure above `y` if and only if its pushforward is universally pure
above `y`. -/
@[stacks 0CVH] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isUniversallyPureAlong_pushforward_iff_of_isClosedImmersion :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
      [Decent f] (i : Z ⟶ X) [IsClosedImmersion i]
      (G : Z.Modules) [G.IsQuasicoherent] [G.IsFiniteType] (y : Points Y),
      G.IsUniversallyPureAlong (i ≫ f) y ↔
        ((pushforward i).obj G).IsUniversallyPureAlong f y)

end AlgebraicGeometry.AlgebraicSpace.Modules
