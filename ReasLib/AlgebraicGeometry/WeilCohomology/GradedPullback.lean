module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w x y z

namespace WeilCohomology.PreWeilTheory

/-- Pullback on a pre-Weil theory restricted to one homogeneous bidegree. -/
noncomputable def pullbackGrade
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X Y : V}
    (f : X ⟶ Y) (p : ℤ × ℤ) : T.Hgrade Y p →ₗ[F] T.Hgrade X p :=
  LinearMap.codRestrict (T.Hgrade X p)
    ((T.pullback f).toLinearMap.domRestrict (T.Hgrade Y p)) (T.pullback_mem f p)

/-- The homogeneous pullback evaluates as the total pullback on every homogeneous class. -/
theorem pullbackGrade_apply
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X Y : V}
    (f : X ⟶ Y) (p : ℤ × ℤ) (a : T.Hgrade Y p) :
    T.pullback f a = T.pullbackGrade f p a := sorry

end WeilCohomology.PreWeilTheory

namespace WeilCohomology.SchemePreWeilTheory

/-- Pullback on a scheme pre-Weil theory restricted to one homogeneous bidegree. -/
noncomputable def pullbackGrade
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
      cyclePullback cyclePushforward pointCycle H Picard) {X Y : V}
    (f : X ⟶ Y) (p : ℤ × ℤ) : T.Hgrade Y p →ₗ[F] T.Hgrade X p :=
  LinearMap.codRestrict (T.Hgrade X p)
    ((T.pullback f).toLinearMap.domRestrict (T.Hgrade Y p)) (T.pullback_mem f p)

/-- The homogeneous scheme pullback evaluates as the total pullback. -/
theorem pullbackGrade_apply
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
      cyclePullback cyclePushforward pointCycle H Picard) {X Y : V}
    (f : X ⟶ Y) (p : ℤ × ℤ) (a : T.Hgrade Y p) :
    T.pullback f a = T.pullbackGrade f p a := sorry

end WeilCohomology.SchemePreWeilTheory
