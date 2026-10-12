/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    T.Hgrade X (2 * (d : ℤ) - i, (d : ℤ) - j) →ₗ[F]
      (T.Hgrade X (i, j) →ₗ[F] F) :=
  ((LinearMap.mul F (H X)).flip.compl₁₂
      (T.Hgrade X (2 * (d : ℤ) - i, (d : ℤ) - j)).subtype
      (T.Hgrade X (i, j)).subtype).compr₂ (T.integral hX)

/-- The Poincare pairing evaluates as cup product followed by the axiom-(A6) trace. -/
theorem poincarePairing_apply
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ)
    (a : T.Hgrade X (2 * (d : ℤ) - i, (d : ℤ) - j))
    (b : T.Hgrade X (i, j)) :
    T.poincarePairing hX i j a b = T.integral hX (b * a) := sorry

/-- Axioms (A1)–(A7) imply finite-dimensionality of every graded cohomology piece. -/
theorem finiteDimensional_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (p : ℤ × ℤ) : Module.Finite F (T.Hgrade X p) := sorry

/-- Axioms (A1)–(A7) imply that every complementary Poincare pairing is bijective. -/
theorem poincarePairing_bijective_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ) :
    Function.Bijective (T.poincarePairing hX i j) := sorry

/-- Axioms (A1)–(A7) give finite-dimensional graded pieces, the cup-trace
evaluation formula, and perfect complementary Poincare pairings. -/
theorem poincareDuality_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) :
    (∀ {X d}, T.IsNonemptyEquidimensional X d → ∀ p : ℤ × ℤ,
      Module.Finite F (T.Hgrade X p)) ∧
    (∀ {X d} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ)
      (a : T.Hgrade X (2 * (d : ℤ) - i, (d : ℤ) - j))
      (b : T.Hgrade X (i, j)),
      T.poincarePairing hX i j a b = T.integral hX (b * a)) ∧
    (∀ {X d} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ),
      Function.Bijective (T.poincarePairing hX i j)) := sorry

end WeilCohomology.SchemePreWeilTheory
