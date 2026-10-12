/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical.Point
import ReasLib.AlgebraicGeometry.Scheme.OverField.Point
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v x y

namespace WeilCohomology

open AlgebraicGeometry CategoryTheory

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {F : Type v} [Field F] [CharZero F]
variable {dimension : SchemeOverField k → ℕ}
variable {product : SchemeOverField k → SchemeOverField k → SchemeOverField k}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {H : SchemeOverField k → Type x} {CH : SchemeOverField k → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : SchemeOverField k},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : SchemeOverField k}, (X ⟶ Y) → CH X →+ CH Y}

variable (T : ClassicalTheory k F (SchemeOverField k) dimension product fst snd
  (SchemeOverField.point k) H CH Hgrade CHgrade cyclePullback cyclePushforward
  (1 : CHgrade (SchemeOverField.point k) 0))

/- Lemma 45.9.4 (1): cohomology of `Spec(k)` vanishes outside degree zero. -/
@[stacks 0FHE] #check
  (WeilCohomology.ClassicalTheory.pointCohomology_isZero T :
    ∀ i : ℤ, i ≠ 0 → Hgrade (SchemeOverField.point k) i = ⊥)

/- Lemma 45.9.4 (2): the canonical algebra equivalence from `F` to
degree-zero cohomology of `Spec(k)` is unique. -/
@[stacks 0FHE] #check
  (WeilCohomology.ClassicalTheory.pointAlgEquiv_unique T :
    ∀ e : F ≃ₐ[F] Hgrade (SchemeOverField.point k) 0,
      e = WeilCohomology.ClassicalTheory.pointAlgEquiv T)

/- Lemma 45.9.4 (3): the cycle class of the fundamental class of `Spec(k)` is one. -/
@[stacks 0FHE] #check
  (WeilCohomology.ClassicalTheory.pointFundamentalCycleClass_eq_one T :
    T.cycleClass (SchemeOverField.point k)
      (1 : CHgrade (SchemeOverField.point k) 0) = 1)

/- Lemma 45.9.4 (4): integration on `Spec(k)` sends one to one. -/
@[stacks 0FHE] #check
  (WeilCohomology.ClassicalTheory.pointIntegral_one T :
    T.integral (SchemeOverField.point k) 1 = 1)

end WeilCohomology
