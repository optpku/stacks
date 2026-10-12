/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w x y z v₁ v₂ x₁ x₂

namespace WeilCohomology.ClassicalTheory

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {F : Type v} [Field F] [CharZero F]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0}

/-- The Betti number of an object in degree `i` for a classical Weil cohomology theory. -/
def bettiNumber
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle)
    (X : V) (i : ℤ) : ℕ :=
  Module.finrank F (Hgrade X i)

/-- `bettiNumber` is the finite dimension of the corresponding homogeneous cohomology group. -/
theorem bettiNumber_eq_finrank
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle)
    (X : V) (i : ℤ) :
    T.bettiNumber X i = Module.finrank F (Hgrade X i) := sorry

variable {F₁ : Type v₁} [Field F₁] [CharZero F₁]
variable {F₂ : Type v₂} [Field F₂] [CharZero F₂]
variable {H₁ : V → Type x₁} {H₂ : V → Type x₂}
variable [∀ X, Ring (H₁ X)] [∀ X, Algebra F₁ (H₁ X)]
variable [∀ X, Ring (H₂ X)] [∀ X, Algebra F₂ (H₂ X)]
variable {Hgrade₁ : ∀ X, ℤ → Submodule F₁ (H₁ X)}
variable {Hgrade₂ : ∀ X, ℤ → Submodule F₂ (H₂ X)}
variable [∀ X, GradedAlgebra (Hgrade₁ X)] [∀ X, GradedAlgebra (Hgrade₂ X)]

/-- Pairwise equality of the Betti numbers assigned to the same object by two classical Weil
cohomology theories. This names the open comparison question without asserting it. -/
def bettiNumbersAgree
    (T₁ : ClassicalTheory k F₁ V dimension product fst snd point H₁ CH Hgrade₁ CHgrade
      cyclePullback cyclePushforward pointCycle)
    (T₂ : ClassicalTheory k F₂ V dimension product fst snd point H₂ CH Hgrade₂ CHgrade
      cyclePullback cyclePushforward pointCycle)
    (X : V) : Prop :=
  ∀ i : ℤ, T₁.bettiNumber X i = T₂.bettiNumber X i

/-- The degreewise characterization of `bettiNumbersAgree`. -/
theorem bettiNumbersAgree_iff
    (T₁ : ClassicalTheory k F₁ V dimension product fst snd point H₁ CH Hgrade₁ CHgrade
      cyclePullback cyclePushforward pointCycle)
    (T₂ : ClassicalTheory k F₂ V dimension product fst snd point H₂ CH Hgrade₂ CHgrade
      cyclePullback cyclePushforward pointCycle)
    (X : V) :
    bettiNumbersAgree T₁ T₂ X ↔
      ∀ i : ℤ, T₁.bettiNumber X i = T₂.bettiNumber X i := sorry

end WeilCohomology.ClassicalTheory
