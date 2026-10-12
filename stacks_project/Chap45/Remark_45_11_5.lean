/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.WeilCohomology.CoefficientFactors
import ReasLib.AlgebraicGeometry.WeilCohomology.Classical.Betti
import StacksCheckRecall

open CategoryTheory

/- Remark 45.11.5
Independence of intermediate coefficient-factor dimensions is the main open question. -/
@[stacks 0FI3] #check (WeilCohomology.CoefficientFactors.intermediateBettiNumbersIndependent :
    ∀ {A : Type} [CommRing A] {r : ℕ} (K : Fin r → Type) [∀ i, Field (K i)]
      (σ : ∀ i, A →+* K i) (hr : 0 < r) (hσ : Function.Bijective (RingHom.pi σ))
      (M : ℤ → ModuleCat A) [∀ n, Module.Finite A (M n)] (d : ℕ), Prop)

#check (WeilCohomology.CoefficientFactors.comparison_bijective :
    ∀ {A : Type} [CommRing A] {r : ℕ} (K : Fin r → Type) [∀ i, Field (K i)]
      (σ : ∀ i, A →+* K i) (hσ : Function.Bijective (RingHom.pi σ))
      (M : ModuleCat A), Function.Bijective
      (WeilCohomology.CoefficientFactors.comparison K σ M))

#check (WeilCohomology.CoefficientFactors.finrank_eq_one_of_rankOne :
    ∀ {A : Type} [CommRing A] {r : ℕ} (K : Fin r → Type) [∀ i, Field (K i)]
      (σ : ∀ i, A →+* K i) (M : ModuleCat A) (e : M ≃ₗ[A] A),
      ∀ i, Module.finrank (K i) ((ModuleCat.extendScalars (σ i)).obj M) = 1)

#check (WeilCohomology.CoefficientFactors.finrank_eq_one_of_duality :
    ∀ {A : Type} [CommRing A] {r : ℕ} (K : Fin r → Type) [∀ i, Field (K i)]
      (σ : ∀ i, A →+* K i) (M : ℤ → ModuleCat A) (d : ℕ)
      (hzero : ∀ i,
        Module.finrank (K i) ((ModuleCat.extendScalars (σ i)).obj (M 0)) = 1)
      (duality : ∀ i,
        (ModuleCat.extendScalars (σ i)).obj (M (2 * (d : ℤ))) ≃ₗ[K i]
          Module.Dual (K i) ((ModuleCat.extendScalars (σ i)).obj (M 0))),
      ∀ i, Module.finrank (K i)
        ((ModuleCat.extendScalars (σ i)).obj (M (2 * (d : ℤ)))) = 1)

#check (WeilCohomology.ClassicalTheory.bettiNumbersAgree :
    ∀ {k : Type} [Field k] [IsAlgClosed k]
      {F₁ : Type} [Field F₁] [CharZero F₁]
      {F₂ : Type} [Field F₂] [CharZero F₂]
      {V : Type} [Category V] {dimension : V → ℕ} {product : V → V → V}
      {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
      {point : V} {H₁ : V → Type} {H₂ : V → Type} {CH : V → Type}
      [∀ X, Ring (H₁ X)] [∀ X, Algebra F₁ (H₁ X)]
      [∀ X, Ring (H₂ X)] [∀ X, Algebra F₂ (H₂ X)]
      [∀ X, CommRing (CH X)]
      {Hgrade₁ : ∀ X, ℤ → Submodule F₁ (H₁ X)}
      {Hgrade₂ : ∀ X, ℤ → Submodule F₂ (H₂ X)}
      {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
      [∀ X, GradedAlgebra (Hgrade₁ X)] [∀ X, GradedAlgebra (Hgrade₂ X)]
      [∀ X, GradedAlgebra (CHgrade X)]
      {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
      {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
      {pointCycle : CHgrade point 0}
      (T₁ : WeilCohomology.ClassicalTheory k F₁ V dimension product fst snd point H₁ CH
        Hgrade₁ CHgrade cyclePullback cyclePushforward pointCycle)
      (T₂ : WeilCohomology.ClassicalTheory k F₂ V dimension product fst snd point H₂ CH
        Hgrade₂ CHgrade cyclePullback cyclePushforward pointCycle)
      (X : V), Prop)
