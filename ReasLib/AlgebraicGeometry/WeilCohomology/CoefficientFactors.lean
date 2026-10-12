/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open CategoryTheory
open scoped ChangeOfRings TensorProduct

noncomputable section

universe u

namespace WeilCohomology.CoefficientFactors

/-- The canonical map from a module to the product of its scalar extensions along a
finite family of coefficient maps. -/
def comparison {A : Type u} [CommRing A] {r : ℕ}
    (K : Fin r → Type u) [∀ i, CommRing (K i)]
    (σ : ∀ i, A →+* K i) (M : ModuleCat.{u} A) :
    M ⟶ ModuleCat.of A
      (∀ i, (ModuleCat.restrictScalars (σ i)).obj
        ((ModuleCat.extendScalars (σ i)).obj M)) :=
  ModuleCat.ofHom <| LinearMap.pi fun i ↦
    ((ModuleCat.extendRestrictScalarsAdj (σ i)).unit.app M).hom

/-- The `i`-th coordinate of `comparison` sends `m` to `1 ⊗ₜ[A, σ i] m`. -/
theorem comparison_apply {A : Type u} [CommRing A] {r : ℕ}
    (K : Fin r → Type u) [∀ i, CommRing (K i)]
    (σ : ∀ i, A →+* K i) (M : ModuleCat.{u} A) (m : M) (i : Fin r) :
    comparison K σ M m i = (1 : K i) ⊗ₜ[A,σ i] m := sorry

/-- A product presentation of the coefficient ring makes `comparison` bijective. -/
theorem comparison_bijective {A : Type u} [CommRing A] {r : ℕ}
    (K : Fin r → Type u) [∀ i, Field (K i)]
    (σ : ∀ i, A →+* K i) (hσ : Function.Bijective (RingHom.pi σ))
    (M : ModuleCat.{u} A) :
    Function.Bijective (comparison K σ M) := sorry

/-- A rank-one module remains one-dimensional after extension to every coefficient field. -/
theorem finrank_eq_one_of_rankOne {A : Type u} [CommRing A] {r : ℕ}
    (K : Fin r → Type u) [∀ i, Field (K i)]
    (σ : ∀ i, A →+* K i) (M : ModuleCat.{u} A) (e : M ≃ₗ[A] A) :
    ∀ i, Module.finrank (K i) ((ModuleCat.extendScalars (σ i)).obj M) = 1 := sorry

/-- Duality with rank-one degree-zero factors forces the top-degree factors to have
dimension one. -/
theorem finrank_eq_one_of_duality {A : Type u} [CommRing A] {r : ℕ}
    (K : Fin r → Type u) [∀ i, Field (K i)]
    (σ : ∀ i, A →+* K i) (M : ℤ → ModuleCat.{u} A) (d : ℕ)
    (hzero : ∀ i,
      Module.finrank (K i) ((ModuleCat.extendScalars (σ i)).obj (M 0)) = 1)
    (duality : ∀ i,
      (ModuleCat.extendScalars (σ i)).obj (M (2 * (d : ℤ))) ≃ₗ[K i]
        Module.Dual (K i) ((ModuleCat.extendScalars (σ i)).obj (M 0))) :
    ∀ i, Module.finrank (K i)
      ((ModuleCat.extendScalars (σ i)).obj (M (2 * (d : ℤ)))) = 1 := sorry

/-- The assertion that the dimensions of all intermediate coefficient factors agree. This
names the open question without asserting that it holds. -/
def intermediateBettiNumbersIndependent {A : Type u} [CommRing A] {r : ℕ}
    (K : Fin r → Type u) [∀ i, Field (K i)]
    (σ : ∀ i, A →+* K i) (hr : 0 < r)
    (hσ : Function.Bijective (RingHom.pi σ))
    (M : ℤ → ModuleCat.{u} A) [∀ n, Module.Finite A (M n)] (d : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n < d → ∀ i j,
    Module.finrank (K i) ((ModuleCat.extendScalars (σ i)).obj (M (n : ℤ))) =
      Module.finrank (K j) ((ModuleCat.extendScalars (σ j)).obj (M (n : ℤ)))

/-- The pointwise characterization of `intermediateBettiNumbersIndependent`. -/
theorem intermediateBettiNumbersIndependent_iff
    {A : Type u} [CommRing A] {r : ℕ}
    (K : Fin r → Type u) [∀ i, Field (K i)]
    (σ : ∀ i, A →+* K i) (hr : 0 < r)
    (hσ : Function.Bijective (RingHom.pi σ))
    (M : ℤ → ModuleCat.{u} A) [∀ n, Module.Finite A (M n)] (d : ℕ) :
    intermediateBettiNumbersIndependent K σ hr hσ M d ↔
      ∀ n : ℕ, 0 < n → n < d → ∀ i j,
        Module.finrank (K i) ((ModuleCat.extendScalars (σ i)).obj (M (n : ℤ))) =
          Module.finrank (K j)
            ((ModuleCat.extendScalars (σ j)).obj (M (n : ℤ))) := sorry

end WeilCohomology.CoefficientFactors
