/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Splitting

open CategoryTheory CategoryTheory.Limits

universe u

open AlgebraicGeometry

/- Lemma 29.48.6: a finite morphism to an affine scheme admits a surjective finite locally free
base change whose pullback embeds into a split finite locally free morphism. -/
@[stacks 03HW] #check
  (AlgebraicGeometry.Scheme.Hom.existsFiniteLocallyFreeCover_hasSplitFiniteLocallyFreeEmbedding :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] (_ : IsFinite f),
      ∃ (X' : Scheme.{u}) (π : X' ⟶ X),
        Surjective π ∧
          IsFiniteLocallyFree π ∧
          Surjective (pullback.fst f π) ∧
          IsFiniteLocallyFree (pullback.fst f π) ∧
          (pullback.snd f π).HasSplitFiniteLocallyFreeEmbedding)
