/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil

@[expose] public section

noncomputable section

universe u v w x y z

open CategoryTheory
open scoped TensorProduct

namespace WeilCohomology.SchemePreWeilTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0} {H Picard : V → Type x}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]

variable (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
  cyclePullback cyclePushforward pointCycle H Picard)

/-- The functional on the target obtained by pulling back, multiplying by a source
class, and integrating over the source. -/
noncomputable def pushforwardFunctional
    {X Y : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (f : X ⟶ Y) :
    H X →ₗ[F] (H Y →ₗ[F] F) :=
  (((LinearMap.mul F (H X)).flip).compl₁₂
    LinearMap.id (T.pullback f).toLinearMap).compr₂ (T.integral hX)

/-- Evaluation of the functional defining cohomological pushforward. -/
theorem pushforwardFunctional_apply
    {X Y : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (f : X ⟶ Y)
    (a : H X) (b : H Y) :
    T.pushforwardFunctional hX f a b = T.integral hX (T.pullback f b * a) := sorry

/-- Contract a functional against the second factor of the target diagonal tensor. -/
noncomputable def diagonalContraction
    {Y : V} {e : ℕ} (hY : T.IsNonemptyEquidimensional Y e) :
    (H Y →ₗ[F] F) →ₗ[F] H Y :=
  (TensorProduct.rid F (H Y)).toLinearMap.comp
    ((LinearMap.applyₗ (T.diagonalTensor hY)).comp (LinearMap.lTensorHom (H Y)))

/-- Diagonal contraction agrees with contraction of the target diagonal tensor. -/
theorem diagonalContraction_apply
    {Y : V} {e : ℕ} (hY : T.IsNonemptyEquidimensional Y e)
    (trace : H Y →ₗ[F] F) :
    T.diagonalContraction hY trace = contractRight trace (T.diagonalTensor hY) := sorry

/-- Cohomological pushforward defined by Poincaré duality from the diagonal tensor and
the source trace pairing. -/
noncomputable def pushforward
    {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) : H X →ₗ[F] H Y :=
  (T.diagonalContraction hY).comp (T.pushforwardFunctional hX f)

/-- Cohomological pushforward is diagonal contraction of its defining functional. -/
theorem pushforward_apply
    {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (a : H X) :
    T.pushforward hX hY f a =
      T.diagonalContraction hY (T.pushforwardFunctional hX f a) := sorry

/-- Poincaré adjunction characterizes cohomological pushforward against the target
trace pairing. -/
theorem pushforward_spec [T.HasDiagonalClassRelation]
    {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (a : H X) (b : H Y) :
    T.integral hY (b * T.pushforward hX hY f a) =
      T.integral hX (T.pullback f b * a) := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- The cycle-class map of a scheme-valued pre-Weil theory commutes with Chow and
cohomological pushforward along a positive-rank projective bundle over a nonempty
equidimensional base. -/
theorem cycleClass_pushforward_of_isProjectiveBundle [T.HasDiagonalClassRelation]
    {P X : V} (p : P ⟶ X) {d r : ℕ} (hr : 0 < r)
    (hp : T.IsProjectiveBundle p r)
    (hX : T.IsNonemptyEquidimensional X d)
    (hP : T.IsNonemptyEquidimensional P (d + r - 1))
    (alpha : CH P) :
    T.cycleClass X (cyclePushforward p alpha) =
      T.pushforward hP hX p (T.cycleClass P alpha) := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry


/-- Cohomological pushforward between the external dimension twists. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedPushforward {X Y : V} {d e : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) (hY : T.IsNonemptyEquidimensional Y e)
    (f : X ⟶ Y) : T.twistedCohomology X d →ₗ[F] T.twistedCohomology Y e :=
  Tate.map T.tateLine_rank (T.pushforward hX hY f) d e

end WeilCohomology.SchemePreWeilTheory
