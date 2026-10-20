module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical

/-!
# Graded cycle-class maps

This module records the restriction of a scheme-valued classical cycle-class map
to a single Chow degree and its prescribed cohomological bidegree.
-/

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology.SchemeClassicalTheory

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

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

/-- The cycle-class homomorphism restricted to codimension `i` cycles and its
prescribed cohomological bidegree `(2 * i, i)`. -/
def gradedCycleClass (X : V) (i : ℤ) :
    CHgrade X i →+ Hgrade X (2 * i, i) :=
  AddMonoidHom.codRestrict
    ((T.cycleClass X).comp (CHgrade X i).subtype.toAddMonoidHom)
    (Hgrade X (2 * i, i)) (T.cycleClass_mem X i)

/-- The graded cycle-class homomorphism agrees with the total cycle-class map
after coercion to total cohomology. -/
theorem gradedCycleClass_apply (X : V) (i : ℤ) (alpha : CHgrade X i) :
    T.gradedCycleClass X i alpha = T.cycleClass X alpha := sorry

end WeilCohomology.SchemeClassicalTheory
