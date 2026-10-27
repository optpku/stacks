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

/-- The Poincare pairing on complementary bidegrees, given by cup product followed by
the trace functional from axiom (A6). -/
noncomputable def poincarePairing
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ) :
    T.Hgrade X (2 * (d : ℤ) - i) →ₗ[F]
      (T.Hgrade X (i) →ₗ[F] F) :=
  ((LinearMap.mul F (H X)).flip.compl₁₂
      (T.Hgrade X (2 * (d : ℤ) - i)).subtype
      (T.Hgrade X (i)).subtype).compr₂ (T.integral hX)

/-- The Poincare pairing evaluates as cup product followed by the axiom-(A6) trace. -/
theorem poincarePairing_apply
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ)
    (a : T.Hgrade X (2 * (d : ℤ) - i))
    (b : T.Hgrade X (i)) :
    T.poincarePairing hX i j a b = T.integral hX (b * a) := sorry

/-- With the explicit diagonal-class mixin, (A1)--(A7) imply finite-dimensional
cohomology pieces. Scheme-level anchoring of the mixin is tracked by RL-2194. -/
theorem finiteDimensional_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) [T.HasDiagonalClassRelation]
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (p : ℤ) : Module.Finite F (T.Hgrade X p) := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- With the explicit diagonal-class mixin, every complementary Poincare
pairing is bijective. Geometric anchoring is tracked by RL-2194. -/
theorem poincarePairing_bijective_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) [T.HasDiagonalClassRelation]
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ) :
    Function.Bijective (T.poincarePairing hX i j) := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- With the explicit diagonal-class mixin, (A1)--(A7) give finite-dimensional
pieces, the cup-trace formula, and perfect complementary pairings. -/
theorem poincareDuality_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) [T.HasDiagonalClassRelation]
     :
    (∀ {X d}, T.IsNonemptyEquidimensional X d → ∀ p : ℤ,
      Module.Finite F (T.Hgrade X p)) ∧
    (∀ {X d} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ)
      (a : T.Hgrade X (2 * (d : ℤ) - i))
      (b : T.Hgrade X (i)),
      T.poincarePairing hX i j a b = T.integral hX (b * a)) ∧
    (∀ {X d} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ),
      Function.Bijective (T.poincarePairing hX i j)) := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry


/-- The Poincare pairing on the external twists n and d-n. The underlying map
is the existing cup-trace coordinate formula; no inverse is chosen. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedPoincarePairing
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (i n : ℤ) :
    T.twistedGrade X (2 * (d : ℤ) - i) ((d : ℤ) - n) →ₗ[F]
      (T.twistedGrade X i n →ₗ[F] F) :=
  (T.poincarePairing hX i n).compl₁₂
    (Tate.trivialization T.tateLine_rank (T.Hgrade X (2 * (d : ℤ) - i))
      ((d : ℤ) - n)).toLinearMap
    (Tate.trivialization T.tateLine_rank (T.Hgrade X i) n).toLinearMap

/-- Poincare duality on complementary external twists under the explicit
diagonal-class mixin; geometric anchoring is tracked by RL-2194. -/
theorem twistedPoincareDuality_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) [T.HasDiagonalClassRelation]
     :
    (∀ {X d}, T.IsNonemptyEquidimensional X d → ∀ i : ℤ,
      Module.Finite F (T.Hgrade X i)) ∧
    (∀ {X d} (hX : T.IsNonemptyEquidimensional X d) (i n : ℤ),
      Function.Bijective (T.twistedPoincarePairing hX i n)) := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

end WeilCohomology.SchemePreWeilTheory
