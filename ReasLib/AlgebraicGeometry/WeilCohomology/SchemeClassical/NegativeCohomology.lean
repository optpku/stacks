/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.SeparatingClosedPoints

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology.SchemeClassicalTheory

open CategoryTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

/-- If some represented object has nonzero cohomology in a negative cohomological
degree for some Tate weight, then some nonempty equidimensional represented
object fails to have separable closed points detecting degree-zero cohomology. -/
theorem exists_not_hasSeparatingClosedPoints_of_negativeCohomology
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    (hneg : ∃ (Y : V) (i j : ℤ), i < 0 ∧ Hgrade Y (i, j) ≠ ⊥) :
    ∃ (X : V) (d : ℕ),
      T.IsNonemptyEquidimensional X d ∧ ¬ T.HasSeparatingClosedPoints X := sorry

end WeilCohomology.SchemeClassicalTheory
