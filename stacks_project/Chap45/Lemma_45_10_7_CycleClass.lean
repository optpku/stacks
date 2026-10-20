module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.OverExtension
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.GradedCycleClass

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w x y z

/- Graded cycle-class homomorphism of a scheme-valued classical Weil cohomology theory. -/
#check (WeilCohomology.SchemeClassicalTheory.gradedCycleClass :
  ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {H : V → Type x} {CH : V → Type y}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
    {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
    [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    (T : WeilCohomology.SchemeClassicalTheory k F TateLine V dimension product fst snd
      point H CH Hgrade CHgrade cyclePullback cyclePushforward)
    (X : V) (i : ℤ), CHgrade X i →+ Hgrade X (2 * i, i))
