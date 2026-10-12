/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.SchemeAxiomA8
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.SchemePushforward

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w x y z

namespace WeilCohomology.SchemePreWeilTheory

/-- For a scheme-valued pre-Weil theory satisfying Axiom A8, the cycle-class
map commutes with Chow pushforward and cohomological pushforward on every
cycle of nonempty equidimensional objects. -/
theorem cycleClass_pushforward_of_axiomsA1ToA8
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0} {H Picard : V → Type x}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    (hA8 : T.SatisfiesAxiomA8) {X Y : V} {d e : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (alpha : CH X) :
    T.cycleClass Y (cyclePushforward f alpha) =
      T.pushforward hX hY f (T.cycleClass X alpha) := sorry

end WeilCohomology.SchemePreWeilTheory
