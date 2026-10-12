/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Lemma_60_25_1
public import stacks_project.Chap60.Lemma_60_25_3_Adjoin
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

/-- Prefer the algebra `D`-module on `D'` so comparison maps match Lemma 60.25.1. -/
noncomputable instance module_inseparableAdjoinCompletion_fromAlgebra
    {D : Type u} [CommRing D] {p : ℕ} {lam : D} :
    Module D (inseparableAdjoinCompletion p lam) :=
  Algebra.toModule

/-- Native `D`-module structure on `Ω_D`. -/
noncomputable instance module_crystallineOmegaD
    {A D : Type u} [CommRing A] [CommRing D]
    {f : A →+* D} {J : Ideal D} {γbar : DividedPowers J}
    {p : ℕ} [Fact (Nat.Prime p)] :
    Module D (crystallineOmegaD f γbar p) :=
  inferInstanceAs
    (Module D (AdicCompletion (Ideal.span {(p : D)}) (dividedPowerDifferential f γbar)))

/-- Restrict scalars of `Ω_D` along `A → D`. -/
noncomputable instance module_crystallineOmegaD_overA
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    {J : Ideal D} {γbar : DividedPowers J} {p : ℕ} [Fact (Nat.Prime p)] :
    Module A (crystallineOmegaD (algebraMap A D) γbar p) :=
  Module.compHom _ (algebraMap A D)

/-- Restrict scalars of `Ω_{D'}` along `D → D'`. -/
noncomputable instance module_inseparableOmega_overD
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    {p : ℕ} [Fact (Nat.Prime p)] {lam : D}
    {J' : Ideal (inseparableAdjoinCompletion p lam)} {γbar' : DividedPowers J'} :
    Module D
      (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar') :=
  Module.compHom _
    (algebraMap D (inseparableAdjoinCompletion p lam))

/-- Scalar tower for the restricted `D`-action on `Ω_{D'}`. -/
instance isScalarTower_inseparableOmega_overD
    (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    (p : ℕ) [Fact (Nat.Prime p)] (lam : D)
    {J' : Ideal (inseparableAdjoinCompletion p lam)} (γbar' : DividedPowers J') :
    @IsScalarTower D (inseparableAdjoinCompletion p lam)
      (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
      Algebra.toSMul _ _ :=
  sorry

/-- Restrict scalars of `Ω_{D'}` along `A → D'`. -/
noncomputable instance module_inseparableOmega_overA
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    {p : ℕ} [Fact (Nat.Prime p)] {lam : D}
    {J' : Ideal (inseparableAdjoinCompletion p lam)} {γbar' : DividedPowers J'} :
    Module A
      (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar') :=
  Module.compHom _
    (algebraMap A (inseparableAdjoinCompletion p lam))

/-- Scalar tower `A → D' → Ω_{D'}`. -/
instance isScalarTower_inseparableOmega_overA
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    {p : ℕ} [Fact (Nat.Prime p)] {lam : D}
    {J' : Ideal (inseparableAdjoinCompletion p lam)} {γbar' : DividedPowers J'} :
    IsScalarTower A (inseparableAdjoinCompletion p lam)
      (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar') :=
  sorry

/-- Scalar tower `A → D → Ω_{D'}`. -/
instance isScalarTower_inseparableOmega_overAD
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    {p : ℕ} [Fact (Nat.Prime p)] {lam : D}
    {J' : Ideal (inseparableAdjoinCompletion p lam)} {γbar' : DividedPowers J'} :
    IsScalarTower A D
      (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar') :=
  sorry

/-- Existence of the 60.25.1 form splitting of `Ω_{D'}`. -/
theorem inseparableFormDecomp_nonempty
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    (p : ℕ) [Fact (Nat.Prime p)] {J : Ideal D} (γbar : DividedPowers J) (lam : D)
    {J' : Ideal (inseparableAdjoinCompletion p lam)} (γbar' : DividedPowers J') :
    Nonempty
      (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar' ≃ₗ[inseparableAdjoinCompletion p lam]
        ((inseparableAdjoinCompletion p lam ⊗[D]
            crystallineOmegaD (algebraMap A D) γbar p) ×
          inseparableAdjoinCompletion p lam)) :=
  sorry

/-- Universal injectivity of `D → D'` as in Lemma 60.25.1. -/
theorem inseparableUniversallyInjective
    {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    LinearMap.UniversallyInjective.{u, u, u, u}
      (Algebra.linearMap D (inseparableAdjoinCompletion p lam)) :=
  sorry

/-- `d(p) = 0` on `Ω_D`, condition (1) of Lemma 60.25.1 with scalar `p`. -/
theorem inseparable_da
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    {J : Ideal D} (γbar : DividedPowers J) (p : ℕ) [Fact (Nat.Prime p)]
    (d : Derivation A D (crystallineOmegaD (algebraMap A D) γbar p)) :
    d (p : D) = 0 :=
  sorry

/-- Canonical comparison `c_M` along `D → D'`, given a 60.25.1 form splitting. -/
noncomputable def inseparableComparison
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    (p : ℕ) [Fact (Nat.Prime p)] {J : Ideal D} (γbar : DividedPowers J) (lam : D)
    {J' : Ideal (inseparableAdjoinCompletion p lam)} (γbar' : DividedPowers J')
    {M : Type u} [AddCommGroup M] [Module D M]
    [Module A (crystallineOmegaD (algebraMap A D) γbar p)]
    [IsScalarTower A D (crystallineOmegaD (algebraMap A D) γbar p)]
    {d : Derivation A D (crystallineOmegaD (algebraMap A D) γbar p)}
    {δ : DifferentialOperator.DeRham.Family A D
      (crystallineOmegaD (algebraMap A D) γbar p)}
    {calculus : ExteriorCalculus d δ} {connection : Connection d M}
    (h_integrable : Connection.IsIntegrable connection calculus)
    (formDecomp :
      inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar' ≃ₗ[inseparableAdjoinCompletion p lam]
        ((inseparableAdjoinCompletion p lam ⊗[D]
            crystallineOmegaD (algebraMap A D) γbar p) ×
          inseparableAdjoinCompletion p lam))
    (targetDifferential : (n : ℕ) →
      tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M n ⟶
        tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M (n + 1))
    (targetSquareZero : ∀ n, targetDifferential n ≫ targetDifferential (n + 1) = 0) :
    Connection.deRhamComplex connection calculus h_integrable ⟶
      tensorDeRhamComplex targetDifferential targetSquareZero :=
  tensorDeRhamComparison h_integrable formDecomp targetDifferential targetSquareZero

/-- Reverse comparison `e_M` from Lemma 60.25.1 with scalar `p`. -/
noncomputable def inseparableHomotopyInverse
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    (p : ℕ) [Fact (Nat.Prime p)] {J : Ideal D} (γbar : DividedPowers J) (lam : D)
    {J' : Ideal (inseparableAdjoinCompletion p lam)} (γbar' : DividedPowers J')
    {M : Type u} [AddCommGroup M] [Module D M]
    [Module A (crystallineOmegaD (algebraMap A D) γbar p)]
    [IsScalarTower A D (crystallineOmegaD (algebraMap A D) γbar p)]
    {d : Derivation A D (crystallineOmegaD (algebraMap A D) γbar p)}
    {δ : DifferentialOperator.DeRham.Family A D
      (crystallineOmegaD (algebraMap A D) γbar p)}
    {calculus : ExteriorCalculus d δ} {connection : Connection d M}
    (h_integrable : Connection.IsIntegrable connection calculus)
    (partialZ : inseparableAdjoinCompletion p lam → inseparableAdjoinCompletion p lam)
    (theta : inseparableAdjoinCompletion p lam →ₗ[D] inseparableAdjoinCompletion p lam)
    (d₁ : inseparableAdjoinCompletion p lam →
      inseparableAdjoinCompletion p lam ⊗[D] crystallineOmegaD (algebraMap A D) γbar p)
    (formDecomp :
      inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar' ≃ₗ[inseparableAdjoinCompletion p lam]
        ((inseparableAdjoinCompletion p lam ⊗[D]
            crystallineOmegaD (algebraMap A D) γbar p) ×
          inseparableAdjoinCompletion p lam))
    (h_universallyInjective :
      LinearMap.UniversallyInjective.{u, u, u, u}
        (Algebra.linearMap D (inseparableAdjoinCompletion p lam)))
    (targetDifferential : (n : ℕ) →
      tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M n ⟶
        tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M (n + 1))
    (targetSquareZero : ∀ n, targetDifferential n ≫ targetDifferential (n + 1) = 0) :
    tensorDeRhamComplex targetDifferential targetSquareZero ⟶
      Connection.deRhamComplex connection calculus h_integrable :=
  tensorDeRhamHomotopyInverse h_integrable (p : D) partialZ theta d₁ formDecomp
    h_universallyInjective targetDifferential targetSquareZero

/-- Degreewise components of the comparison `c_M`. -/
theorem inseparableComparison_apply
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    (p : ℕ) [Fact (Nat.Prime p)] {J : Ideal D} (γbar : DividedPowers J) (lam : D)
    {J' : Ideal (inseparableAdjoinCompletion p lam)} (γbar' : DividedPowers J')
    {M : Type u} [AddCommGroup M] [Module D M]
    [Module A (crystallineOmegaD (algebraMap A D) γbar p)]
    [IsScalarTower A D (crystallineOmegaD (algebraMap A D) γbar p)]
    {d : Derivation A D (crystallineOmegaD (algebraMap A D) γbar p)}
    {δ : DifferentialOperator.DeRham.Family A D
      (crystallineOmegaD (algebraMap A D) γbar p)}
    {calculus : ExteriorCalculus d δ} {connection : Connection d M}
    (h_integrable : Connection.IsIntegrable connection calculus)
    (formDecomp :
      inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar' ≃ₗ[inseparableAdjoinCompletion p lam]
        ((inseparableAdjoinCompletion p lam ⊗[D]
            crystallineOmegaD (algebraMap A D) γbar p) ×
          inseparableAdjoinCompletion p lam))
    (targetDifferential : (n : ℕ) →
      tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M n ⟶
        tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M (n + 1))
    (targetSquareZero : ∀ n, targetDifferential n ≫ targetDifferential (n + 1) = 0)
    (n : ℕ) :
    (inseparableComparison p γbar lam γbar' h_integrable formDecomp
        targetDifferential targetSquareZero).f n =
      tensorDeRhamComparisonComponent connection formDecomp n :=
  sorry

/-- Degreewise components of the reverse comparison `e_M`. -/
theorem inseparableHomotopyInverse_apply
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    (p : ℕ) [Fact (Nat.Prime p)] {J : Ideal D} (γbar : DividedPowers J) (lam : D)
    {J' : Ideal (inseparableAdjoinCompletion p lam)} (γbar' : DividedPowers J')
    {M : Type u} [AddCommGroup M] [Module D M]
    [Module A (crystallineOmegaD (algebraMap A D) γbar p)]
    [IsScalarTower A D (crystallineOmegaD (algebraMap A D) γbar p)]
    {d : Derivation A D (crystallineOmegaD (algebraMap A D) γbar p)}
    {δ : DifferentialOperator.DeRham.Family A D
      (crystallineOmegaD (algebraMap A D) γbar p)}
    {calculus : ExteriorCalculus d δ} {connection : Connection d M}
    (h_integrable : Connection.IsIntegrable connection calculus)
    (partialZ : inseparableAdjoinCompletion p lam → inseparableAdjoinCompletion p lam)
    (theta : inseparableAdjoinCompletion p lam →ₗ[D] inseparableAdjoinCompletion p lam)
    (d₁ : inseparableAdjoinCompletion p lam →
      inseparableAdjoinCompletion p lam ⊗[D] crystallineOmegaD (algebraMap A D) γbar p)
    (formDecomp :
      inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar' ≃ₗ[inseparableAdjoinCompletion p lam]
        ((inseparableAdjoinCompletion p lam ⊗[D]
            crystallineOmegaD (algebraMap A D) γbar p) ×
          inseparableAdjoinCompletion p lam))
    (h_universallyInjective :
      LinearMap.UniversallyInjective.{u, u, u, u}
        (Algebra.linearMap D (inseparableAdjoinCompletion p lam)))
    (targetDifferential : (n : ℕ) →
      tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M n ⟶
        tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M (n + 1))
    (targetSquareZero : ∀ n, targetDifferential n ≫ targetDifferential (n + 1) = 0)
    (n : ℕ) :
    (inseparableHomotopyInverse p γbar lam γbar' h_integrable partialZ theta d₁ formDecomp
        h_universallyInjective targetDifferential targetSquareZero).f n =
      tensorDeRhamHomotopyInverseComponent connection (p : D) partialZ theta d₁ formDecomp
        h_universallyInjective n :=
  sorry

/-- Optional exact equality `e_M ∘ c_M = ·p` on the source complex. -/
theorem inseparableHomotopyInverse_comp_comparison_eq_scalar
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    (p : ℕ) [Fact (Nat.Prime p)] {J : Ideal D} (γbar : DividedPowers J) (lam : D)
    {J' : Ideal (inseparableAdjoinCompletion p lam)} (γbar' : DividedPowers J')
    {M : Type u} [AddCommGroup M] [Module D M]
    [Module A (crystallineOmegaD (algebraMap A D) γbar p)]
    [IsScalarTower A D (crystallineOmegaD (algebraMap A D) γbar p)]
    {d : Derivation A D (crystallineOmegaD (algebraMap A D) γbar p)}
    {δ : DifferentialOperator.DeRham.Family A D
      (crystallineOmegaD (algebraMap A D) γbar p)}
    {calculus : ExteriorCalculus d δ} {connection : Connection d M}
    (h_integrable : Connection.IsIntegrable connection calculus)
    (partialZ : inseparableAdjoinCompletion p lam → inseparableAdjoinCompletion p lam)
    (theta : inseparableAdjoinCompletion p lam →ₗ[D] inseparableAdjoinCompletion p lam)
    (d₁ : inseparableAdjoinCompletion p lam →
      inseparableAdjoinCompletion p lam ⊗[D] crystallineOmegaD (algebraMap A D) γbar p)
    (formDecomp :
      inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar' ≃ₗ[inseparableAdjoinCompletion p lam]
        ((inseparableAdjoinCompletion p lam ⊗[D]
            crystallineOmegaD (algebraMap A D) γbar p) ×
          inseparableAdjoinCompletion p lam))
    (h_universallyInjective :
      LinearMap.UniversallyInjective.{u, u, u, u}
        (Algebra.linearMap D (inseparableAdjoinCompletion p lam)))
    (targetDifferential : (n : ℕ) →
      tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M n ⟶
        tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M (n + 1))
    (targetSquareZero : ∀ n, targetDifferential n ≫ targetDifferential (n + 1) = 0) :
    inseparableComparison p γbar lam γbar' h_integrable formDecomp targetDifferential
        targetSquareZero ≫
      inseparableHomotopyInverse p γbar lam γbar' h_integrable partialZ theta d₁ formDecomp
        h_universallyInjective targetDifferential targetSquareZero =
      tensorDeRhamScalar h_integrable (p : D) :=
  sorry

/-- Lemma 60.25.3 (1): `c_M ∘ e_M` is homotopic to multiplication by `p` on the
`D'`-side tensor de Rham complex, for `D'` the `p`-adic completion of
`D[z]⟨ξ⟩ / (ξ - (z^p - lam))` and `Ω_{D'}` the `p`-adic completion of
divided-power differentials of `D'` over `A`. -/
@[stacks 07N1]
noncomputable def homotopy_comparison_comp_inverse_p
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    (p : ℕ) [Fact (Nat.Prime p)] {J : Ideal D} (γbar : DividedPowers J) (lam : D)
    {J' : Ideal (inseparableAdjoinCompletion p lam)} (γbar' : DividedPowers J')
    {M : Type u} [AddCommGroup M] [Module D M]
    [Module A (crystallineOmegaD (algebraMap A D) γbar p)]
    [IsScalarTower A D (crystallineOmegaD (algebraMap A D) γbar p)]
    {d : Derivation A D (crystallineOmegaD (algebraMap A D) γbar p)}
    {δ : DifferentialOperator.DeRham.Family A D
      (crystallineOmegaD (algebraMap A D) γbar p)}
    {calculus : ExteriorCalculus d δ} {connection : Connection d M}
    (h_integrable : Connection.IsIntegrable connection calculus)
    (partialZ : inseparableAdjoinCompletion p lam → inseparableAdjoinCompletion p lam)
    (theta : inseparableAdjoinCompletion p lam →ₗ[D] inseparableAdjoinCompletion p lam)
    (d₁ : inseparableAdjoinCompletion p lam →
      inseparableAdjoinCompletion p lam ⊗[D] crystallineOmegaD (algebraMap A D) γbar p)
    (formDecomp :
      inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar' ≃ₗ[inseparableAdjoinCompletion p lam]
        ((inseparableAdjoinCompletion p lam ⊗[D]
            crystallineOmegaD (algebraMap A D) γbar p) ×
          inseparableAdjoinCompletion p lam))
    (h_universallyInjective :
      LinearMap.UniversallyInjective.{u, u, u, u}
        (Algebra.linearMap D (inseparableAdjoinCompletion p lam)))
    (targetDifferential : (n : ℕ) →
      tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M n ⟶
        tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M (n + 1))
    (targetSquareZero : ∀ n, targetDifferential n ≫ targetDifferential (n + 1) = 0) :
    Homotopy
      (inseparableHomotopyInverse p γbar lam γbar' h_integrable partialZ theta d₁ formDecomp
          h_universallyInjective targetDifferential targetSquareZero ≫
        inseparableComparison p γbar lam γbar' h_integrable formDecomp targetDifferential
          targetSquareZero)
      (tensorDeRhamTargetScalar targetDifferential targetSquareZero (p : D)) where
  hom := tensorDeRhamHomotopyHom theta formDecomp
  zero := fun _ _ _ ↦ sorry
  comm := fun _ ↦ sorry

/-- Lemma 60.25.3 (2): `e_M ∘ c_M` is homotopic to multiplication by `p` on the
`D`-side tensor de Rham complex, for `D'` the `p`-adic completion of
`D[z]⟨ξ⟩ / (ξ - (z^p - lam))` and `Ω_{D'}` as in 60.17.0.2. -/
@[stacks 07N1]
noncomputable def homotopy_inverse_comp_comparison_p
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    (p : ℕ) [Fact (Nat.Prime p)] {J : Ideal D} (γbar : DividedPowers J) (lam : D)
    {J' : Ideal (inseparableAdjoinCompletion p lam)} (γbar' : DividedPowers J')
    {M : Type u} [AddCommGroup M] [Module D M]
    [Module A (crystallineOmegaD (algebraMap A D) γbar p)]
    [IsScalarTower A D (crystallineOmegaD (algebraMap A D) γbar p)]
    {d : Derivation A D (crystallineOmegaD (algebraMap A D) γbar p)}
    {δ : DifferentialOperator.DeRham.Family A D
      (crystallineOmegaD (algebraMap A D) γbar p)}
    {calculus : ExteriorCalculus d δ} {connection : Connection d M}
    (h_integrable : Connection.IsIntegrable connection calculus)
    (partialZ : inseparableAdjoinCompletion p lam → inseparableAdjoinCompletion p lam)
    (theta : inseparableAdjoinCompletion p lam →ₗ[D] inseparableAdjoinCompletion p lam)
    (d₁ : inseparableAdjoinCompletion p lam →
      inseparableAdjoinCompletion p lam ⊗[D] crystallineOmegaD (algebraMap A D) γbar p)
    (formDecomp :
      inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar' ≃ₗ[inseparableAdjoinCompletion p lam]
        ((inseparableAdjoinCompletion p lam ⊗[D]
            crystallineOmegaD (algebraMap A D) γbar p) ×
          inseparableAdjoinCompletion p lam))
    (h_universallyInjective :
      LinearMap.UniversallyInjective.{u, u, u, u}
        (Algebra.linearMap D (inseparableAdjoinCompletion p lam)))
    (targetDifferential : (n : ℕ) →
      tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M n ⟶
        tensorDeRhamTargetTerm D
          (inseparableOmega p lam (algebraMap A (inseparableAdjoinCompletion p lam)) γbar')
          M (n + 1))
    (targetSquareZero : ∀ n, targetDifferential n ≫ targetDifferential (n + 1) = 0) :
    Homotopy
      (inseparableComparison p γbar lam γbar' h_integrable formDecomp targetDifferential
          targetSquareZero ≫
        inseparableHomotopyInverse p γbar lam γbar' h_integrable partialZ theta d₁ formDecomp
          h_universallyInjective targetDifferential targetSquareZero)
      (tensorDeRhamScalar h_integrable (p : D)) :=
  Homotopy.ofEq
    (inseparableHomotopyInverse_comp_comparison_eq_scalar p γbar lam γbar' h_integrable
      partialZ theta d₁ formDecomp h_universallyInjective targetDifferential
      targetSquareZero)
