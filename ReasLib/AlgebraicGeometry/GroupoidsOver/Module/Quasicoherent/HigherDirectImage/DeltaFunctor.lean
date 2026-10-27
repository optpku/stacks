/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Abelian

/-! # Adjunction and cohomological connecting maps for quasi-coherent direct images -/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComposableArrows
open scoped Bicategory

noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Quasi-coherent pullback along a quasi-compact quasi-separated morphism
is adjoint to inclusion, module direct image, and the quasi-coherent coreflector.
The small-section certificate is the original-universe size convention. -/
theorem QCoh.pullback_directImage_adjunction {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] :
    Nonempty (QCoh.pullback f ⊣ QCoh.directImage f) :=
  sorry

/-- Quasi-coherent pullback along a quasi-compact quasi-separated morphism
is a left adjoint, with quasi-coherent direct image as its specified right adjoint. -/
instance QCoh.pullback_isLeftAdjoint {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] :
    (QCoh.pullback f).IsLeftAdjoint where
  exists_rightAdjoint := ⟨QCoh.directImage f, QCoh.pullback_directImage_adjunction f⟩

/-- Quasi-coherent higher direct images have connecting morphisms natural
in short exact sequences, with initial monicity and every five-arrow exactness
window. Size and resolution certificates implement the original-universe convention. -/
theorem QCoh.exists_higherDirectImageConnecting {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)] :
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
            ((AdditiveFunctor.of (QCoh.higherDirectImageFunctor f (n + 1))).obj.map φ.τ₁)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
