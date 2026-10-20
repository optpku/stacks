/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Separation
import StacksCheckRecall

/-!
# Quasi-separated and separated morphisms of completions

If a morphism of algebraic spaces is quasi-separated or separated, then the
induced morphism of formal completions along a closed subset is likewise
quasi-separated or separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

/- Lemma 88.23.7 (1): If `f : X' ⟶ X` is quasi-separated, then the induced
morphism `completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is quasi-separated. -/
@[stacks 0GDG] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiSeparated_completionAlongMap :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
      [AlgebraicSpace.QuasiSeparated f] (T : Closeds (Points X)),
      FormalAlgebraicSpace.QuasiSeparated (completionAlong.map f T))

/- Lemma 88.23.7 (2): If `f : X' ⟶ X` is separated, then the induced morphism
`completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is separated. -/
@[stacks 0GDG] #check
  (AlgebraicGeometry.AlgebraicSpace.separated_completionAlongMap :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
      [AlgebraicSpace.Separated f] (T : Closeds (Points X)),
      FormalAlgebraicSpace.Separated (completionAlong.map f T))
