/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.K0.Conormal

@[expose] public section

noncomputable section

universe u v w x y z

open AlgebraicGeometry CategoryTheory

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

/-- The cycle-class map of a scheme-valued pre-Weil theory commutes with
pushforward on all cycles once it does so for the unit of every closed
immersion of nonempty equidimensional objects whose conormal `K₀`-class
extends from the target. -/
theorem cycleClass_pushforward_of_conormalClass
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) [T.HasDiagonalClassRelation]
    (h_conormal : ∀ {Z X : V} {d e : ℕ}
      (hZ : T.IsNonemptyEquidimensional Z d)
      (hX : T.IsNonemptyEquidimensional X e) (i : Z ⟶ X)
      [IsClosedImmersion (T.scheme.map i).left],
      (T.scheme.map i).left.ConormalClassExtends →
        T.pushforward hZ hX i (1 : H Z) =
          T.cycleClass X (cyclePushforward i (1 : CHgrade Z 0)))
    {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (alpha : CH X) :
    T.pushforward hX hY f (T.cycleClass X alpha) =
      T.cycleClass Y (cyclePushforward f alpha) := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

end WeilCohomology.SchemePreWeilTheory
