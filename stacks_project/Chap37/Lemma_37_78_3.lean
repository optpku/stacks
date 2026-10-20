/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CompletelyDecomposed
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

/- Lemma 37.78.3: a completely decomposed family of scheme morphisms remains
completely decomposed after base change along an arbitrary morphism. -/
@[stacks 0GTK] #check
  (AlgebraicGeometry.CompletelyDecomposedFamily.pullback :
    ∀ {I : Type v} {Y Y' : AlgebraicGeometry.Scheme.{u}}
      (X : I → AlgebraicGeometry.Scheme.{u})
      (π : ∀ i, X i ⟶ Y) [AlgebraicGeometry.CompletelyDecomposedFamily X π]
      (g : Y' ⟶ Y),
      AlgebraicGeometry.CompletelyDecomposedFamily (fun i ↦ pullback (π i) g)
        (fun i ↦ pullback.snd (π i) g))
