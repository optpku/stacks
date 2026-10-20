/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.InDimensions
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 38.20.9: for a finite-type quasicoherent module over a locally finite-type
morphism, the fibrewise nonflat loci have dimension less than `n` exactly when the module
is flat over the base in dimensions at least `n`. -/
@[stacks 0CWF] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverInDimensionsGE_iff_fiberNonflatLocus_dim_lt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}}
      (ℱ : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ),
      AlgebraicGeometry.Scheme.Modules.flatOverInDimensionsGE ℱ f n ↔
        ∀ s : S,
          topologicalKrullDim
              (AlgebraicGeometry.Scheme.Modules.fiberNonflatLocus ℱ f s) <
            (n : WithBot ℕ∞))

/- The flatness-in-dimensions condition is preserved by arbitrary scheme base change. -/
#check
  (AlgebraicGeometry.Scheme.Modules.flatOverInDimensionsGE_pullback :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}}
      (ℱ : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (n : ℕ) (g : S' ⟶ S),
      AlgebraicGeometry.Scheme.Modules.flatOverInDimensionsGE ℱ f n →
      AlgebraicGeometry.Scheme.Modules.flatOverInDimensionsGE
        (AlgebraicGeometry.Scheme.Modules.baseChangeModule f g ℱ) (pullback.snd f g) n)
