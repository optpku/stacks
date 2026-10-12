/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.NegativeCohomology
import StacksCheckRecall

@[expose] public section

universe u v w x y z

open AlgebraicGeometry CategoryTheory

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
variable (T : WeilCohomology.SchemeClassicalTheory k F TateLine V dimension product
  fst snd point H CH Hgrade CHgrade cyclePullback cyclePushforward)

/- Lemma 45.11.3
nonzero cohomology in a negative cohomological degree for some Tate weight
yields a nonempty equidimensional represented scheme for which separable
closed points do not detect degree-zero cohomology. -/
@[stacks 0FI1] #check
  (WeilCohomology.SchemeClassicalTheory.exists_not_hasSeparatingClosedPoints_of_negativeCohomology :
    ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
      {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
      {V : Type w} [Category.{z} V] {dimension : V → ℕ} {product : V → V → V}
      {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
      {point : V} {H : V → Type x} {CH : V → Type y}
      [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
      {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
      {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
      [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
      {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
      {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
      (T : WeilCohomology.SchemeClassicalTheory k F TateLine V dimension product
        fst snd point H CH Hgrade CHgrade cyclePullback cyclePushforward),
      (∃ (Y : V) (i j : ℤ), i < 0 ∧ Hgrade Y (i, j) ≠ ⊥) →
        ∃ (X : V) (d : ℕ),
          T.IsNonemptyEquidimensional X d ∧ ¬ T.HasSeparatingClosedPoints X)
