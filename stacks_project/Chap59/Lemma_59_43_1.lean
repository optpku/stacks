/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallPushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SmallToBig

universe u

/- Lemma 59.43.1: if a morphism of schemes `f : X ⟶ Y` has property (B), then
   the direct image functor `f_small,*` on sheaves of sets over the small étale
   sites preserves surjective (locally surjective) morphisms. -/
@[stacks 04DO] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism_pushforward_preservesLocallySurjective_of_hasPropertyB :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology (Type (u + 1))]
      (hB : hasPropertyB f),
      (smallMorphism f).pushforward.PreservesLocallySurjective)
