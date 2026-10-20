/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace WeilCohomology.PreWeilTheory

/-- The functional on target cohomology obtained by pulling back, multiplying by a source
class, and integrating over the source. -/
noncomputable def pushforwardFunctional
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X Y : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) (f : X ⟶ Y) :
    H X →ₗ[F] (H Y →ₗ[F] F) :=
  (((LinearMap.mul F (H X)).flip).compl₁₂
    LinearMap.id (T.pullback f).toLinearMap).compr₂ (T.integral hX)

/-- Evaluation of the functional used to define cohomological pushforward. -/
theorem pushforwardFunctional_apply
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X Y : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) (f : X ⟶ Y) (a : H X) (c : H Y) :
    T.pushforwardFunctional hX f a c =
      T.integral hX (T.pullback f c * a) := sorry

/-- Contract a functional against the second factor of the diagonal tensor. -/
noncomputable def diagonalContraction
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {Y : V} {d : ℕ}
    (hY : T.IsNonemptyEquidimensional Y d) :
    (H Y →ₗ[F] F) →ₗ[F] H Y :=
  (TensorProduct.rid F (H Y)).toLinearMap.comp
    ((LinearMap.applyₗ (T.diagonalTensor hY)).comp
      (LinearMap.lTensorHom (H Y)))

/-- Diagonal contraction agrees with contraction of the diagonal tensor. -/
theorem diagonalContraction_apply
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {Y : V} {d : ℕ}
    (hY : T.IsNonemptyEquidimensional Y d) (trace : H Y →ₗ[F] F) :
    T.diagonalContraction hY trace =
      WeilCohomology.contractRight trace (T.diagonalTensor hY) := sorry

/-- Cohomological pushforward obtained from the diagonal tensor and the trace pairing. -/
noncomputable def pushforward
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X Y : V} {d e : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) :
    H X →ₗ[F] H Y :=
  (T.diagonalContraction hY).comp (T.pushforwardFunctional hX f)

/-- Cohomological pushforward is diagonal contraction of its defining functional. -/
theorem pushforward_apply
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X Y : V} {d e : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (a : H X) :
    T.pushforward hX hY f a =
      T.diagonalContraction hY (T.pushforwardFunctional hX f a) := sorry

end WeilCohomology.PreWeilTheory
