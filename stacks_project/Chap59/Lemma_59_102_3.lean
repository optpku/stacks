/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.SmallEtale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 59.102.3: For a proper morphism of schemes, the canonical comparison
between small étale and big ph pushforward is an isomorphism. -/
@[stacks 0DDY] #check
  (AlgebraicGeometry.Scheme.PhComparison.proper_smallPhPushforward_isIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology (Type (u + 1))]
      [HasSheafify Y.smallEtaleTopology (Type (u + 1))] [IsProper f],
      IsIso (AlgebraicGeometry.Scheme.PhComparison.smallPhPushforwardHom f))
