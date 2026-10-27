/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage.DeltaFunctor
public import stacks_project.Chap103.Proposition_103_11_1_DirectImage
import StacksCheckRecall

/-! # Pushforward of quasi-coherent modules on algebraic stacks -/

open AlgebraicGeometry CategoryTheory ComposableArrows
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u
variable {S : Scheme.{u}}

/- Proposition 103.11.1: quasi-coherent pullback has the specified direct-image
right adjoint along a quasi-compact quasi-separated morphism of algebraic stacks. -/
@[stacks 077A] #check (AlgebraicGeometry.GroupoidsOver.QCoh.pullback_directImage_adjunction :
    ∀ {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f],
    Nonempty (QCoh.pullback f ⊣ QCoh.directImage f))

/- Proposition 103.11.1: the higher direct images have all the connecting maps
and laws of a cohomological delta-functor. -/
@[stacks 077A] #check (AlgebraicGeometry.GroupoidsOver.QCoh.exists_higherDirectImageConnecting :
    ∀ {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)],
    ∃ δ : ∀ ⦃S : ShortComplex (QCoh X)⦄ (hS : S.ShortExact) (n : ℕ),
        (AdditiveFunctor.of (QCoh.higherDirectImageFunctor f n)).obj.obj S.X₃ ⟶
          (AdditiveFunctor.of (QCoh.higherDirectImageFunctor f (n + 1))).obj.obj S.X₁,
      (∀ ⦃S : ShortComplex (QCoh X)⦄ (hS : S.ShortExact),
          Mono ((AdditiveFunctor.of (QCoh.higherDirectImageFunctor f 0)).obj.map S.f)) ∧
      (∀ ⦃S : ShortComplex (QCoh X)⦄ (hS : S.ShortExact) (n : ℕ),
          (mk₅ ((AdditiveFunctor.of (QCoh.higherDirectImageFunctor f n)).obj.map S.f)
            ((AdditiveFunctor.of (QCoh.higherDirectImageFunctor f n)).obj.map S.g) (δ hS n)
            ((AdditiveFunctor.of (QCoh.higherDirectImageFunctor f (n + 1))).obj.map S.f)
            ((AdditiveFunctor.of (QCoh.higherDirectImageFunctor f (n + 1))).obj.map S.g)).Exact) ∧
      (∀ ⦃S T : ShortComplex (QCoh X)⦄ (hS : S.ShortExact) (hT : T.ShortExact)
          (φ : S ⟶ T) (n : ℕ),
          CommSq ((AdditiveFunctor.of (QCoh.higherDirectImageFunctor f n)).obj.map φ.τ₃)
            (δ hS n) (δ hT n)
            ((AdditiveFunctor.of (QCoh.higherDirectImageFunctor f (n + 1))).obj.map φ.τ₁)))
