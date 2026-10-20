/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
public import stacks_project.Chap103.Proposition_103_11_1_DirectImage

/-!
# Pushforward of quasi-coherent modules on algebraic stacks

A quasi-compact quasi-separated 1-morphism of algebraic stacks has a
quasi-coherent direct image right adjoint to pullback, and the higher
direct images form a cohomological δ-functor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComposableArrows
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The quasi-coherent pullback along a quasi-compact quasi-separated morphism
of algebraic stacks is left adjoint to `QCoh.directImage`. -/
theorem QCoh.pullback_directImage_adjunction {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    Nonempty (QCoh.pullback f ⊣ QCoh.directImage f) :=
  sorry

/-- Proposition 103.11.1 (1): let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and
quasi-separated morphism of algebraic stacks. The functor
`QCoh.pullback f : QCoh 𝒴 ⥤ QCoh 𝒳` has a right adjoint
`QCoh.directImage f`, the composition
`QCoh.toLQCohFbc 𝒳 ⋙ LQCohFbc.directImage f ⋙ LQCohFbc.toQCoh 𝒴`. -/
@[stacks 077A]
instance QCoh.pullback_isLeftAdjoint {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (QCoh.pullback f).IsLeftAdjoint where
  exists_rightAdjoint := ⟨QCoh.directImage f, QCoh.pullback_directImage_adjunction f⟩

/-- Connecting morphisms making `QCoh.higherDirectImageFunctor f` a
cohomological δ-functor. -/
theorem QCoh.exists_higherDirectImageConnecting {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
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

/-- Proposition 103.11.1 (2): defining `R^i f_{QCoh,*}` as
`QCoh.higherDirectImageFunctor f i`, the family `{R^i f_{QCoh,*}}_{i ≥ 0}`
is a cohomological δ-functor. -/
@[stacks 077A]
def QCoh.higherDirectImageDeltaFunctor {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    CohomologicalDeltaFunctor (QCoh X) (QCoh Y) where
  F n := AdditiveFunctor.of (QCoh.higherDirectImageFunctor f n)
  δ := (QCoh.exists_higherDirectImageConnecting f).choose
  mono_map_f_zero := (QCoh.exists_higherDirectImageConnecting f).choose_spec.1
  exact₅ := (QCoh.exists_higherDirectImageConnecting f).choose_spec.2.1
  δ_naturality := (QCoh.exists_higherDirectImageConnecting f).choose_spec.2.2

/-- The degree-`n` functor of `QCoh.higherDirectImageDeltaFunctor f` is the
additive packaging of `QCoh.higherDirectImageFunctor f n`. -/
theorem QCoh.higherDirectImageDeltaFunctor_F {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (n : ℕ) :
    (QCoh.higherDirectImageDeltaFunctor f).F n =
      AdditiveFunctor.of (QCoh.higherDirectImageFunctor f n) :=
  rfl

end AlgebraicGeometry.GroupoidsOver
