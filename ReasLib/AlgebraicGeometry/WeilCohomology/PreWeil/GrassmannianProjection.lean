module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.SchemePushforward
public import ReasLib.AlgebraicGeometry.Grassmannian.BaseChange

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w x y z

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

/-- A presentation object isomorphic to the Grassmannian `G(l, n)` over `k` is
nonempty equidimensional of dimension `l * (n - l)`. -/
theorem grassmannian_isNonemptyEquidimensional
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {l n : ℕ} {hl : 0 < l} {hln : l < n}
    (P : Grassmannian.Model.{u} l n hl hln) {G : V}
    (eG : T.scheme.obj G ≅ Over.mk (Grassmannian.toBase P (Spec (.of k)))) :
    T.IsNonemptyEquidimensional G (l * (n - l)) := sorry

/-- The cycle-class map commutes with pushforward along the projection of a
product with `G(l, n)`. -/
theorem cycleClass_pushforward_grassmannianProjection
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {l n : ℕ} {hl : 0 < l} {hln : l < n}
    (P : Grassmannian.Model.{u} l n hl hln) {G X : V}
    (eG : T.scheme.obj G ≅ Over.mk (Grassmannian.toBase P (Spec (.of k))))
    {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (alpha : CH (product X G)) :
    T.cycleClass X (cyclePushforward (fst X G) alpha) =
      T.pushforward
        (T.product_isNonemptyEquidimensional hX
          (T.grassmannian_isNonemptyEquidimensional P eG))
        hX (fst X G) (T.cycleClass (product X G) alpha) := sorry

end WeilCohomology.SchemePreWeilTheory
